/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.TapeMachine
public import NLAlib.Eigensolvers.SpectralBisection.UpStepData
public import NLAlib.Matrix.FinitePrecision.SpectralBisection.Levels

/-!
# Mathematical levels and stored node records

The pure path traversal determines which nodes occupy a level. Its representation stores
actual size literals and packed node matrices, zero in absent slots, and the two mathematical
level parameters. Records refer directly to the existing stored-outcome predicate. These
predicates describe mathematical nodes and outcomes, without execution-phase state records.

## Main results

* `NLAlib.SpectralBisection.StoresLevel`: the input nodes of a mathematical level.
* `NLAlib.SpectralBisection.StoresRecords`: the actual outcomes of its occupied positive nodes.
* `NLAlib.SpectralBisection.storesRecords_of_word_steps`: actual batch words give indexed records.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Store every reached mathematical node, zero size in every absent slot, and the two level
parameters. The scalar machine supplies the actual literal words; no decoding exactness is
built into this storage predicate. -/
def StoresLevel {K : Type} (M : Machine K) (F : FloatMachine K ℕ ℕ)
    (n fuel : ℕ) (R0 beta : K) (root : EighNode K) (d : ℕ) (ma sz lv : ℕ × ℕ)
    (m : Mem K) : Prop :=
  (∀ (a : List Bool) lo (x : EighNode K), a.length = d →
    eighLoc F n fuel R0 beta 0 0 root a = some (lo, x) →
      m.store.get sz.1 (sz.2 + n * d + lo) = some (M.lit (x.k : ℚ)) ∧
        m.store.readBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo) (2 * (x.k * x.k)) =
          some ((EntryCodec.pair K).packFinMatrix x.A)) ∧
  (∀ lo < n, (∀ (a : List Bool) (x : EighNode K), a.length = d →
    eighLoc F n fuel R0 beta 0 0 root a ≠ some (lo, x)) →
      m.store.get sz.1 (sz.2 + n * d + lo) = some (M.lit 0)) ∧
  m.store.readBlock lv.1 (lv.2 + 2 * d) 2 =
    some [(eighLevelParams F R0 root.ε root.ℓ d).1,
      (eighLevelParams F R0 root.ε root.ℓ d).2]

/-- Every reached positive node has its exact mathematical step outcome represented by the
actual matrix, value and metadata tuple of `StoresStep`. -/
def StoresRecords {K : Type} (M : Machine K) (F : FloatMachine K ℕ ℕ)
    (n fuel : ℕ) (R0 beta : K) (root : EighNode K) (d : ℕ)
    (ma ua qa ea sz kd kp : ℕ × ℕ) (m : Mem K) : Prop :=
  ∀ (a : List Bool) lo (x : EighNode K), a.length = d →
    eighLoc F n fuel R0 beta 0 0 root a = some (lo, x) → 0 < x.k →
      StoresStep M x.R n d lo ma ua qa ea sz kd kp
        (eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo)) m

/-- Agreement below the arena handles preserves all mathematical level inputs. -/
theorem StoresLevel.of_below {K : Type} {M : Machine K} {F : FloatMachine K ℕ ℕ}
    {n fuel d L : ℕ} {R0 beta : K} {root : EighNode K} {ma sz lv : ℕ × ℕ}
    {m m' : Mem K} (hBelow : Store.Below L m.store m'.store)
    (hMa : ma.1 < L) (hSz : sz.1 < L) (hLv : lv.1 < L)
    (h : StoresLevel M F n fuel R0 beta root d ma sz lv m) :
    StoresLevel M F n fuel R0 beta root d ma sz lv m' := by
  refine ⟨?_, ?_, (hBelow.readBlock hLv _ _).trans h.2.2⟩
  · intro a lo x ha hx
    have hn := h.1 a lo x ha hx
    exact ⟨((hBelow sz.1 hSz).2 _).trans hn.1, (hBelow.readBlock hMa _ _).trans hn.2⟩
  · intro lo hlo habsent
    exact ((hBelow sz.1 hSz).2 _).trans (h.2.1 lo hlo habsent)

/-- Zero-depth initialization stores precisely the mathematical root and no other occupied
slot. The root size cell is explicit even for an empty root matrix. -/
theorem storesLevel_zero {K : Type} (M : Machine K) (F : FloatMachine K ℕ ℕ)
    {n fuel : ℕ} {R0 eps beta : K} {ell : ℕ} (A : Matrix (Fin n) (Fin n) (K × K))
    {ma sz lv : ℕ × ℕ} {m : Mem K}
    (hA : m.store.readBlock ma.1 ma.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix A))
    (hSz : m.store.get sz.1 sz.2 = some (M.lit (n : ℚ)))
    (hOther : ∀ lo < n, lo ≠ 0 → m.store.get sz.1 (sz.2 + lo) = some (M.lit 0))
    (hParams : m.store.readBlock lv.1 lv.2 2 = some [R0, eps]) :
    StoresLevel M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ 0 ma sz lv m := by
  refine ⟨?_, ?_, ?_⟩
  · intro a lo x ha hx
    obtain rfl : a = [] := List.eq_nil_of_length_eq_zero ha
    simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    simpa only [Nat.mul_zero, Nat.add_zero] using And.intro hSz hA
  · intro lo hlo habsent
    have hne : lo ≠ 0 := by
      intro hzero
      subst lo
      exact habsent [] _ rfl rfl
    simpa only [Nat.mul_zero, Nat.add_zero] using hOther lo hlo hne
  · simpa only [Nat.mul_zero, Nat.add_zero, eighLevelParams] using hParams

/-- Actual raw-word step outcomes on the stored level batches give the exact indexed-tape
records. The root's pure slot-bound theorem justifies every used Gaussian component. -/
theorem storesRecords_of_word_steps {K : Type} [Inhabited K] (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (n base : ℕ) (τ : Tape K)
    (fuel : ℕ) (R0 eps beta : K) (ell : ℕ) (A : Matrix (Fin n) (Fin n) (K × K))
    (d : ℕ) (ma ua qa ea sz kd kp : ℕ × ℕ) (m : Mem K)
    (h : ∀ (a : List Bool) lo (x : EighNode K), a.length = d →
      eighLoc (tapeMachine M dec mm qr n base τ) n fuel R0 beta 0 0
        ⟨n, A, R0, eps, ell⟩ a = some (lo, x) → 0 < x.k →
      StoresStep M x.R n d lo ma ua qa ea sz kd kp
        (eighStep (M.toFloatMachine dec mm qr M.mul
          (fun z : K × K => M.normalWords z.1 z.2)) n fuel R0 beta x.A x.R x.ε x.ℓ
          (storedNodeSample n lo (vec (levelUniformWords n base τ d) lo)
            (levelGaussianMatrix n base τ d))) m) :
    StoresRecords M (tapeMachine M dec mm qr n base τ) n fuel R0 beta
      ⟨n, A, R0, eps, ell⟩ d ma ua qa ea sz kd kp m := by
  intro a lo x ha hx hpos
  have hslot := (add_k_le_and_of_eighLoc hx).1
  rw [eighStep_tapeMachine M dec mm qr n base τ d lo fuel R0 beta x.R x.ε x.ℓ x.A hslot]
  exact h a lo x ha hx hpos

/-- Disjoint writes preserve all records at a level whenever they protect the recorded
outcome regions of each reached positive mathematical node. -/
theorem StoresRecords.of_eqOff {K : Type} {M : Machine K} {F : FloatMachine K ℕ ℕ}
    {n fuel d : ℕ} {R0 beta : K} {root : EighNode K} {ma ua qa ea sz kd kp : ℕ × ℕ}
    {m m' : Mem K} {G : Fp} (hfr : m.store.EqOff G m'.store)
    (hdis : ∀ (a : List Bool) lo (x : EighNode K), a.length = d →
      eighLoc F n fuel R0 beta 0 0 root a = some (lo, x) → 0 < x.k →
      Fp.Disj G (Fp.blocks
        (stepOutputs n d lo ma ua qa ea sz kd kp
          (eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo)))
        (stepOutputLengths (eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ
          (eighTapeSample n d lo)))))
    (h : StoresRecords M F n fuel R0 beta root d ma ua qa ea sz kd kp m) :
    StoresRecords M F n fuel R0 beta root d ma ua qa ea sz kd kp m' := by
  intro a lo x ha hx hpos
  exact (h a lo x ha hx hpos).of_eqOff hfr (hdis a lo x ha hx hpos)

end NLAlib.SpectralBisection
