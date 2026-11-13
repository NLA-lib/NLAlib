import proposals.polar.Adjoint
import proposals.polar.Packed
import NLAlib.Computation.BLAS
import NLAlib.Computation.StaticCost
import NLAlib.Matrix.Computation.KernelContracts
import NLAlib.Matrix.Functions.PolarMinimax
import Mathlib.Data.Finsupp.Weight

/-! Review candidate for the matrix-product count in the odd minimax polar iteration.
This standalone file is outside the library and does not declare a registered target. -/

open NLAlib NLAlib.Computation NLAlib.Computation.Builder

namespace Proposal.Polar

/-- Remaining Horner multiplications, reading coefficients in descending order. -/
def inner {VB VI : Type} (n d base : IExp VI) (coeff gram poly tmp : VB) :
    Builder Unit Unit VB VI Unit :=
  forRange d fun j => do
    stmt (.kcall () () [n, n, n] [(gram, 0), (poly, 0)] [(tmp, 0)])
    addDiagonal n tmp coeff (base + (d - 1 - .var j))
    copyv () tmp 0 poly 0 (n * n)

/-- One Horner polar iteration from the packed stage coefficients. -/
def stage {VB VI : Type} (m n d index : IExp VI) (X coeff adj gram poly tmp : VB) :
    Builder Unit Unit VB VI Unit := do
  let base := index * (d + 2)
  adjoint m n X adj
  stmt (.kcall () () [n, m, n] [(adj, 0), (X, 0)] [(gram, 0)])
  scaleMatrix n n gram poly coeff (base + d + 1)
  addDiagonal n poly coeff (base + d)
  inner n d base coeff gram poly tmp
  stmt (.kcall () () [m, n, n] [(X, 0), (poly, 0)] [(adj, 0)])
  copyv () adj 0 X 0 (m * n)

/-- The iterate uses degree d+1. The matrix is read once from column-major ROM, while the
coefficient block stores each stage in ascending order, starting at position stage*(d+2).
Both real and complex data use one exact scalar word per entry. -/
def horner {VB VI : Type} (m n d stages : IExp VI) (X coeff : VB) :
    Builder Unit Unit VB VI Unit := do
  forRange (m * n) fun i => stmt (.rom () ⟨X, .var i⟩ (.var i))
  scope do
    let adj ← alloc () (m * n)
    let gram ← alloc () (n * n)
    let poly ← alloc () (n * n)
    let tmp ← alloc () (n * n)
    forRange stages fun i => stage m n d (.var i) X coeff adj gram poly tmp

/-- One compiled tree with four symbolic sizes and two declared buffers. -/
def horner.compiled : Prog Unit Unit 3 2 :=
  (ProgFamily.compile fun _ _ m sizes handles =>
    (horner m (sizes 0) (sizes 1) (sizes 2) (handles 0) (handles 1)).run).get rfl

/-- The compiled tree instantiates to the displayed builder at every size. -/
theorem horner.toStmt_compiled (m n d k : ℕ) :
    horner.compiled.toStmt m ![n, d, k] = (horner (.const m) (.const n) (.const d)
      (.const k) 0 1).run := rfl

private theorem weight_sequence {α : Type} (xs : List α) (c : α → StaticCost Unit Unit)
    (weight : OpKind Unit Unit → ℕ) :
    Finsupp.weight weight (StaticCost.sequence xs c).count =
      (xs.map fun i => Finsupp.weight weight (c i).count).sum := by
  induction xs with
  | nil => simp [StaticCost.sequence, StaticCost.zero]
  | cons x xs ih => simp [StaticCost.sequence, StaticCost.seq, ih]

/-- The compiled tree's standard static count gives each actual black-box matrix
multiplication weight one. All other operation kinds have kernel weight zero. -/
theorem horner.kernelWeight_staticCost (m n d k : ℕ) (width : Unit → ℕ) :
    Finsupp.weight (OpKind.kernelWeight fun _ => 1)
      (horner.compiled.staticCost (fun op => Finsupp.single op 1) width m ![n,d,k]).count =
      (d + 2) * k := by
  change Finsupp.weight _ (StaticCost.seq _ _).count = _
  simp only [FStmt.staticCost, StaticCost.seq, StaticCost.alloc, StaticCost.step, StaticCost.zero,
    weight_sequence, map_add, Finsupp.weight_single, OpKind.kernelWeight,
    Instr.subst, Instr.kind, IExp.evalIn, add_zero,
    Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty, Matrix.Fin.cons_vecCons,
    List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]
  simp [Matrix.cons_val]
  ring


/-- The program has no data-dependent control flow. -/
private def fixedLoops {nb ni : ℕ} : FStmt Unit Unit nb ni → Bool
  | .skip | .instr _ | .rom .. | .kcall .. => true
  | .seq a b => fixedLoops a && fixedLoops b
  | .loop _ body | .alloc _ _ body | .named _ _ body => fixedLoops body
  | _ => false

private theorem count_fold {K α : Type} (f : St Unit K (OpCount Unit Unit) → α →
    Option (St Unit K (OpCount Unit Unit))) (cost : α → StaticCost Unit Unit)
    (h : ∀ i st out, f st i = some out → out.cnt = st.cnt + (cost i).count) (xs : List α)
    {st out : St Unit K (OpCount Unit Unit)} (run : xs.foldlM f st = some out) :
    out.cnt = st.cnt + (StaticCost.sequence xs cost).count := by
  induction xs generalizing st with
  | nil => cases run; simp [StaticCost.sequence, StaticCost.zero]
  | cons x xs ih =>
    obtain ⟨mid, head, tail⟩ := Option.bind_eq_some_iff.mp run
    rw [ih tail, h x st mid head]
    simp [StaticCost.sequence, StaticCost.seq, add_assoc]

private theorem count_of_fixedLoops {K : Type} (I : Interp Unit Unit K (OpCount Unit Unit)) :
    ∀ {nb ni : ℕ} (tree : FStmt Unit Unit nb ni) (buf : Fin nb → ℕ) (idx : Fin ni → ℕ)
      {st out : St Unit K (OpCount Unit Unit)}, fixedLoops tree = true →
      tree.exec I buf idx st = some out →
      out.cnt = st.cnt + (tree.staticCost I.charge I.width idx).count
  | _, _, .skip, _, _, _, _, _, h => by cases h; simp [FStmt.staticCost, StaticCost.zero]
  | _, _, .seq a b, buf, idx, _, _, hf, h => by
    obtain ⟨mid, head, tail⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hf
    rw [count_of_fixedLoops I b buf idx hb tail, count_of_fixedLoops I a buf idx ha head]
    simp [FStmt.staticCost, StaticCost.seq, add_assoc]
  | _, _, .instr i, _, _, _, _, _, h => by
    obtain ⟨v, _, rfl⟩ := Option.map_eq_some_iff.mp h
    cases i <;> rfl
  | _, _, .rom .., _, _, _, _, _, h => by
    simp only [FStmt.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    rfl
  | _, _, .alloc _ _ body, _, _, _, _, hf, h => by
    obtain ⟨o, run, rfl⟩ := Option.map_eq_some_iff.mp h
    have hc := count_of_fixedLoops I body _ _ hf run
    exact hc
  | _, _, .loop _ body, _, _, _, _, hf, h => by
    exact count_fold _ _ (fun i _ _ run => count_of_fixedLoops I body _ _ hf run) _ h
  | _, _, .named _ _ body, _, _, _, _, hf, h => count_of_fixedLoops I body _ _ hf h
  | _, _, .kcall .., _, _, _, _, _, h => by
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  | _, _, .whileFuel .., _, _, _, _, hf, _ => by contradiction
  | _, _, .bindIdx .., _, _, _, _, hf, _ => by contradiction
  | _, _, .ite .., _, _, _, _, hf, _ => by contradiction
  | _, _, .apply .., _, _, _, _, hf, _ => by contradiction

/-- Every successful run of the displayed tree adds exactly (d+2)k matrix products to its
initial count, including zero stages and degree one. The kernel weight ignores scalar arithmetic. -/
theorem horner.kernelWeight_cnt_of_exec_eq_some {K : Type} (I : Interp Unit Unit K (OpCount Unit Unit))
    (std : I.charge = fun op => Finsupp.single op 1) (m n d k : ℕ)
    {st out : St Unit K (OpCount Unit Unit)}
    (run : horner.compiled.exec I m ![n,d,k] st = some out) :
    Finsupp.weight (OpKind.kernelWeight fun _ => 1) out.cnt =
      Finsupp.weight (OpKind.kernelWeight fun _ => 1) st.cnt + (d+2)*k := by
  have always : fixedLoops horner.compiled = true := rfl
  have h := count_of_fixedLoops I horner.compiled _ _ always run
  change out.cnt = st.cnt + (horner.compiled.staticCost I.charge I.width m ![n, d, k]).count at h
  rw [h, map_add, std]
  exact congrArg (_ + ·) (horner.kernelWeight_staticCost m n d k I.width)

/-- The proposed success, correctness, and cost obligation. A maintainer must approve a
stored-entries access model with an exact multiplication kernel before registry admission. -/
def StoredEntriesHornerWithExactMM : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (m n d k : ℕ) (c : ℕ → ℕ → ℝ) (vals : ℕ → 𝕜) (ξ : Dist → ℕ → ℝ),
    letI : Inhabited 𝕜 := ⟨0⟩
    horner.compiled.RunsWithin
      ((storedInterp (m * n) vals ξ ()).withKernel ()
        (liftMM realLayout (exactMM (𝕜 := 𝕜))) (mmShape (realLayout (K := 𝕜))))
      m ![n,d,k] (inputState () [Array.replicate (m * n) none,
        Array.ofFn fun t : Fin (k * (d+2)) => some ((c (t / (d+2)) (t % (d+2)) : ℝ) : 𝕜)])
      (horner.compiled.staticCost (fun op => Finsupp.single op 1) (fun _ => 0) m ![n,d,k]).count
      (fun _ => 3*m*n + 3*n*n + k*(d+2))
      (fun out => realLayout.Holds out.store () 0 0
        (oddMatrixIterate (d+1) c (Matrix.of fun (i : Fin m) (j : Fin n) => vals (i + m*j)) k) ∧
        Finsupp.weight (OpKind.kernelWeight fun _ => 1) out.cnt = (d+2)*k)


end Proposal.Polar
