/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Certification
public import NLAlib.Ops.Logic.ContextSnapshot
public import Mathlib.Data.List.OfFn

/-!
# Raw context prefixes for canonical problems

Context words are supplied as initialized raw buffers before the original buffer interface.
The original admissibility relation is applied to the shifted tail. Additional mathematical
input conditions, such as symmetry or positive definiteness of the stored matrix, are explicit
and require an actual raw-input witness at every admitted size. No buffer initializer or
matrix decoder runs during input construction.

## Main results

* `NLAlib.Ops.Problem.withContext`: prefix a raw problem with declared context buffers.
* `NLAlib.Ops.Problem.withContext.originalInput`: recover the original raw input relation.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K : Type} {r b : ℕ}

/-- Prefix supplied context data to the original raw buffers, retaining all mathematical
admission conditions and requiring a real joint witness at each valid size. -/
def Problem.withContext (P : Problem K r b) (count : ℕ)
    (lengths : (Fin r → ℕ) → Fin count → ℕ)
    (extra : (d : Fin r → ℕ) → (Fin count → List K) → P.Data d → Prop)
    (supply : ∀ d, P.valid d → ∃ context : Fin count → List K, ∃ x : P.Input d,
      (∀ i, (context i).length = lengths d i) ∧ extra d context x.val.1) :
    Problem K r (count + b) where
  formats := Fin.append (fun _ => .cell) P.formats
  valid := P.valid
  Data d := (Fin count → List K) × P.Data d
  admissible d data buffers :=
    (∀ i, buffers (Fin.castAdd b i) = (data.1 i).map some) ∧
    P.admissible d data.2 (fun j => buffers (Fin.natAdd count j)) ∧
    (∀ i, (data.1 i).length = lengths d i) ∧ extra d data.1 data.2
  admitted := P.admitted
  supply d hd := by
    obtain ⟨context, x, hlen, hextra⟩ := supply d hd
    refine ⟨(context, x.val.1), Fin.append (fun i => (context i).map some) x.val.2,
      ?_, ?_, hlen, hextra⟩
    · intro i
      exact Fin.append_left _ _ i
    · simpa only [Fin.append_right] using x.property

namespace Problem.withContext

variable {P : Problem K r b} {count : ℕ}
  {lengths : (Fin r → ℕ) → Fin count → ℕ}
  {extra : (d : Fin r → ℕ) → (Fin count → List K) → P.Data d → Prop}
  {supply : ∀ d, P.valid d → ∃ context : Fin count → List K, ∃ x : P.Input d,
    (∀ i, (context i).length = lengths d i) ∧ extra d context x.val.1}

/-- The shifted tail is an ordinary input to the original problem; no word is changed. -/
def originalInput {d : Fin r → ℕ} (x : (P.withContext count lengths extra supply).Input d) :
    P.Input d := ⟨⟨x.val.1.2, fun j => x.val.2 (Fin.natAdd count j)⟩, x.property.2.1⟩

/-- Additional mathematical admission facts concern the actual raw context words. -/
theorem extra_input {d : Fin r → ℕ} (x : (P.withContext count lengths extra supply).Input d) :
    extra d x.val.1.1 x.val.1.2 := x.property.2.2.2

/-- The supplied context words have their declared lengths. -/
theorem length_context {d : Fin r → ℕ} (x : (P.withContext count lengths extra supply).Input d)
    (i : Fin count) : (x.val.1.1 i).length = lengths d i := x.property.2.2.1 i

/-- The actual supplied buffer array is its context prefix followed by the original tail. -/
theorem buffers_eq {d : Fin r → ℕ} (x : (P.withContext count lengths extra supply).Input d) :
    x.val.2 = Fin.append (fun i => (x.val.1.1 i).map some) (originalInput x).val.2 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    exact x.property.1 j
  · rw [Fin.append_right]
    rfl

/-- The canonical store contains exactly the explicitly supplied context and original buffers. -/
theorem initial_store {d : Fin r → ℕ} (x : (P.withContext count lengths extra supply).Input d) :
    ((P.withContext count lengths extra supply).initial d x).store =
      List.ofFn (fun i => (x.val.1.1 i).map some) ++ (P.initial d (originalInput x)).store := by
  change List.ofFn x.val.2 = _
  rw [buffers_eq, List.ofFn_fin_append]
  rfl

/-- Initial context reads return the supplied raw words at their declared size. -/
theorem initial_readBlock_context (d : Fin r → ℕ)
    (x : (P.withContext count lengths extra supply).Input d) (i : Fin count) :
    ((P.withContext count lengths extra supply).initial d x).store.readBlock i.val 0
      (lengths d i) = some (x.val.1.1 i) := by
  have h := Problem.initial_readBlock d x (Fin.castAdd b i) (x.property.1 i)
  rw [length_context x i] at h
  exact h

/-- Initial context capacities count every supplied word. -/
theorem initial_len_context (d : Fin r → ℕ)
    (x : (P.withContext count lengths extra supply).Input d) (i : Fin count) :
    ((P.withContext count lengths extra supply).initial d x).store.len i.val = lengths d i := by
  have h := Problem.initial_len d x (Fin.castAdd b i)
  rw [x.property.1 i, List.length_map, length_context x i] at h
  exact h

/-- A supplied original buffer retains its capacity at the shifted handle. -/
theorem initial_len_original (d : Fin r → ℕ)
    (x : (P.withContext count lengths extra supply).Input d) (i : Fin b) :
    ((P.withContext count lengths extra supply).initial d x).store.len (count + i.val) =
      (P.initial d (originalInput x)).store.len i.val := by
  have h := Problem.initial_len d x (Fin.natAdd count i)
  have hOld := Problem.initial_len d (originalInput x) i
  exact h.trans hOld.symm

/-- Read a supplied original raw word buffer through its shifted handle. -/
theorem initial_readBlock_original (d : Fin r → ℕ)
    (x : (P.withContext count lengths extra supply).Input d) (i : Fin b) {words : List K}
    (h : (originalInput x).val.2 i = words.map some) :
    ((P.withContext count lengths extra supply).initial d x).store.readBlock (count + i.val)
      0 words.length = some words :=
  Problem.initial_readBlock d x (Fin.natAdd count i) h

/-- Resident payload includes every supplied context word and every original buffer,
including uninitialized output capacity. Forwarding itself performs no initialization. -/
theorem initialBytes_eq (d : Fin r → ℕ)
    (x : (P.withContext count lengths extra supply).Input d) :
    (P.withContext count lengths extra supply).initialBytes d x =
      (List.ofFn (lengths d)).sum + P.initialBytes d (originalInput x) := by
  have h : (fun i : Fin (count + b) =>
      ((P.withContext count lengths extra supply).formats i).bytes * (x.val.2 i).length) =
      Fin.append (lengths d)
        (fun i => (P.formats i).bytes * ((originalInput x).val.2 i).length) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      change (Fin.append (fun _ => StorageFormat.cell) P.formats (Fin.castAdd b j)).bytes *
        (x.val.2 (Fin.castAdd b j)).length = _
      rw [Fin.append_left, Fin.append_left, x.property.1 j, List.length_map,
        length_context x j]
      simp [StorageFormat.bytes, StorageFormat.cell]
    · intro j
      change (Fin.append (fun _ => StorageFormat.cell) P.formats (Fin.natAdd count j)).bytes *
        (x.val.2 (Fin.natAdd count j)).length = _
      rw [Fin.append_right, Fin.append_right]
      rfl
  unfold Problem.initialBytes
  rw [h, List.ofFn_fin_append, List.sum_append]

end Problem.withContext

end NLAlib.Ops
