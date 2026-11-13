import proposals.polar.Diagonal
import NLAlib.Computation.BLAS

/-! Packed copies, scalar multiplication, and the Horner suffix recurrence. -/

open NLAlib NLAlib.Computation NLAlib.Computation.Builder

namespace Proposal.Polar

private def packedValue {K : Type} [Zero K] {l n : ℕ} (A : Matrix (Fin l) (Fin n) K) (t : ℕ) : K :=
  if h : 0 < l ∧ t < n*l then A ⟨t % l, Nat.mod_lt _ h.1⟩ ⟨t / l, (Nat.div_lt_iff_lt_mul h.1).mpr h.2⟩
  else 0

private theorem packedValue_index {K : Type} [Zero K] {l n : ℕ} (A : Matrix (Fin l) (Fin n) K)
    (i : Fin l) (j : Fin n) : packedValue A (i + l*j) = A i j := by
  have h : i.val + l*j < n*l := by nlinarith [Nat.mul_le_mul_left l j.isLt, i.isLt]
  simp [packedValue, Fin.pos i, h, Nat.mod_eq_of_lt i.isLt, Nat.add_mul_div_left, Nat.div_eq_of_lt i.isLt]

private theorem read_packedValue {K : Type} [Zero K] {l n b : ℕ} {s : Store Unit K}
    {A : Matrix (Fin l) (Fin n) K} (h : realLayout.Holds s () b 0 A) (t : ℕ) (ht : t < l*n) :
    s.read () b t = some (packedValue A t) := by
  have hl : 0 < l := by by_contra! he; simp [Nat.eq_zero_of_le_zero he] at ht
  rw [Nat.mul_comm] at ht
  let i : Fin l := ⟨t % l, Nat.mod_lt _ hl⟩
  let j : Fin n := ⟨t / l, (Nat.div_lt_iff_lt_mul hl).mpr ht⟩
  have ri := (oneWordHolds_iff _ _ _).mp h i j
  simpa [packedValue, i, j, hl, ht, Nat.mod_add_div] using ri

private theorem holds_packedValue {K : Type} [Zero K] {l n b : ℕ} {s : Store Unit K}
    (A : Matrix (Fin l) (Fin n) K) (h : ∀ t < l*n, s.read () b t = some (packedValue A t)) :
    realLayout.Holds s () b 0 A := by
  refine (oneWordHolds_iff _ _ _).mpr fun i j => ?_
  have ht : i.val + l*j < l*n := by nlinarith [Nat.mul_le_mul_left l j.isLt, i.isLt]
  simpa [packedValue_index] using h _ ht

/-- A contiguous one-word matrix copy between distinct buffers. -/
theorem spec_copyMatrix {K C : Type} [RCLike K] [AddMonoid C] (md : Mode)
    (I : Interp Unit Unit K C) {l n : ℕ} (src dst : ℕ) (hne : src ≠ dst)
    (A : Matrix (Fin l) (Fin n) K) :
    RoutineSpec md I (fun st => realLayout.Holds st.store () src 0 A ∧
      md.Needs (Writable st.store () dst 0 (l*n)))
      (copyv () src 0 dst 0 (.const l * .const n)) [matBlock dst 0 l n 1]
      fun st out => realLayout.Holds out.store () dst 0 A ∧ PosKept st out := by
  have hc := spec_forRange_copy (m := md) (I := I) (p := ())
    (n := .const l * .const n) (Y := dst) (off := 0) (X := src)
    (didx := fun i => 0 + .var i) (sidx := fun i => 0 + .var i) (packedValue A)
    (fun _ => rfl) (fun _ _ => blockDisjoint_of_fst_ne hne)
  apply (RoutineSpec.named "copy" _ hc.spec).conseq
  · intro st hs
    exact ⟨by simpa [IExp.eval] using read_packedValue hs.1, hs.2⟩
  · simp [matBlock, IExp.eval]
  · intro st out _ hp
    exact ⟨holds_packedValue A (by simpa using hp.1), hp.2⟩

/-- Write a scalar multiple of a whole packed matrix into a separate destination. -/
def scaleMatrix {VB VI : Type} (l n : IExp VI) (src dst coef : VB) (off : IExp VI) :
    Builder Unit Unit VB VI Unit :=
  forRange (l*n) fun i => ins (.bin () .mul ⟨dst, .var i⟩ ⟨src, .var i⟩ ⟨coef, off⟩)

/-- Both modes of the packed scalar multiplication, preserving its input and coefficient. -/
theorem spec_scaleMatrix {K C : Type} [RCLike K] [AddMonoid C] (md : Mode)
    (I : Interp Unit Unit K C) (hs : I.sem = exactSem) {l n : ℕ} (src dst coef : ℕ)
    (hsd : src ≠ dst) (hcd : coef ≠ dst) (off : IExp ℕ) (A : Matrix (Fin l) (Fin n) K) (z : K) :
    RoutineSpec md I (fun st => realLayout.Holds st.store () src 0 A ∧
      st.store.read () coef off.eval = some z ∧ md.Needs (Writable st.store () dst 0 (l*n)))
      (scaleMatrix (.const l) (.const n) src dst coef off) [matBlock dst 0 l n 1]
      fun st out => realLayout.Holds out.store () dst 0 (z • A) ∧ PosKept st out := by
  let : Inhabited K := ⟨0⟩
  have hc := spec_forRange_bin (m := md) (I := I) (p := ()) (op := .mul)
    (n := .const l * .const n) (Y := dst) (off := 0) (X := src) (c := ⟨coef,off⟩)
    (didx := fun i => .var i) (sidx := fun i => .var i) (packedValue A) z
    (fun i => by simp) (fun _ _ => blockDisjoint_of_fst_ne hsd) (blockDisjoint_of_fst_ne hcd)
  apply hc.conseq
  · intro st h
    exact ⟨read_packedValue h.1, h.2.1, h.2.2.mono fun hw =>
      ⟨fun i _ => ⟨_, by rw [hs]; rfl⟩, hw⟩⟩
  · simp [matBlock, IExp.eval]
  · intro st out _ h
    refine ⟨(oneWordHolds_iff _ _ _).mpr fun i j => ?_, h.2⟩
    have ht : i.val + l*j < l*n := by nlinarith [Nat.mul_le_mul_left l j.isLt, i.isLt]
    have hv := h.1 (i+l*j) ht
    simpa [hs, exactSem, packedValue_index, mul_comm] using hv

end Proposal.Polar
