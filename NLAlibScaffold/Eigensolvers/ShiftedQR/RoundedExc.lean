/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedKernels
public import NLAlibScaffold.Matrix.QRIteration.Strategy
public import NLAlib.Ops.Logic.IndependentLoop
public import NLAlibScaffold.Matrix.FinitePrecision.ProductRounded
public import NLAlibScaffold.Eigensolvers.ShiftedQR.PairBlocks

/-!
# The rounded exceptional shifts

The exceptional shifts $\mathrm{Exc}$ of [BanksGarzaVargasSrivastava2022, Lemma 5.3] are a net
of a disk around the promising Ritz value $r$, translated by one uniform sample $w$ of a small
disk and rounded. The translate makes every shift forward stable: a separated net, translated
at random, keeps away from the $n$ eigenvalues except with a small probability.

The program `NLAlib.ShiftedQR.excShifts` takes the net as global data (the paper's "fixed
overhead"): the square grid `NLAlib.ShiftedQR.excNet ε` of radius $1.3$ and spacing parameter
$3\varepsilon/4$, scaled by the radius word $\tilde R$. The translate has radius
$\varepsilon\tilde R/2$, so the translated grid still covers $\mathbb{D}(r, \tilde R)$ at
radius $0.975\,\varepsilon\tilde R$, leaving $0.005\,\varepsilon\tilde R$ (and more) for
rounding; the grid points stay $0.99$ times the translate radius apart, the separation the
random translate needs; and the grid has at most $9/\varepsilon^2$ points without being
intersected with a disk. These are the corrections G13i–iii of the errata to the paper's
covering budget.

## Main definitions

* `NLAlib.ShiftedQR.excShifts`: the program; `NLAlib.ShiftedQR.excNet`: its net.
* `NLAlib.ShiftedQR.excCentreWord`, `NLAlib.ShiftedQR.excShiftWord`,
  `NLAlib.ShiftedQR.excSample`: the computed centre, shifts and sample.

## Main results

* `NLAlib.ShiftedQR.excTranslate_bad_window_le`: the window of two uniform draws that the polar
  sampler maps to a translate bringing some net point within
  $\eta = \varepsilon R\sqrt{\varphi/(11n)}$ of an eigenvalue has probability at most
  $\varphi$.
* `NLAlib.ShiftedQR.excShifts_writes_word`: the stored shifts on any scalar machine.
* `NLAlib.ShiftedQR.norm_excShiftWord_sub_le`: the rounding error of one shift.
* `NLAlib.ShiftedQR.excShifts_pwrites`: except with probability $\varphi$, the stored shifts
  cover $\mathbb{D}(r, \tilde R)$ at radius $\varepsilon\tilde R$, are at most
  $9/\varepsilon^2$, and keep a distance from every eigenvalue.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib.ShiftedQR

/-- **The translate of the exceptional shifts fails with probability at most $\varphi$**
(the random translate of [BanksGarzaVargasSrivastava2022, Lemma 5.3], with the packing count
$11$ of errata G13iii for the paper's $3$): let $S$ be a finite set whose distinct points are at
distance at least $0.99\,\varepsilon R$, $\varepsilon R > 0$, $\lambda_1, \dots, \lambda_n$
complex numbers, $0 \le \varphi \le 1/5$ and $\eta = \varepsilon R\sqrt{\varphi/(11n)}$. For two
independent uniform draws $x_0, x_1 \in [0, 1]$ and the polar sample
$w = \varepsilon R\sqrt{x_0}\,e^{2\pi i x_1}$, uniform on $\mathbb{D}(0, \varepsilon R)$,
$$\mathbb{P}[\exists s \in S,\ \exists i,\ \lvert s + w - \lambda_i\rvert < \eta] \le
\varphi.$$
The bound $\varphi \le 1/5$ makes $\eta \le 0.14\,\varepsilon R$, the radius up to which the
packing count holds. -/
theorem excTranslate_bad_window_le (S : Finset ℂ) {N : ℕ} (e : Fin N → ℂ) {ε R φ : ℝ}
    (hεR : 0 < ε * R) (hφ : 0 ≤ φ) (hφ1 : φ ≤ 1 / 5)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 0.99 * (ε * R) ≤ ‖a - b‖) :
    (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Icc 0 1)).real
      {x | ∃ s ∈ S, ∃ i, ‖s + polarDisk 0 (ε * R) x - e i‖ < ε * R * √(φ / (11 * N))} ≤ φ := by
  classical
  set η := ε * R * √(φ / (11 * N)) with hη_def
  set Λ : Finset ℂ := Finset.univ.image e
  have hΛ : (Λ.card : ℝ) ≤ N := by
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin N))) (f := e)
    simpa [Λ] using (Nat.cast_le (α := ℝ)).mpr this
  have hη0 : 0 ≤ η := by positivity
  have hq0 : 0 ≤ φ / (11 * N) := by positivity
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [measureReal_def, hφ]
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq : φ / (11 * N) ≤ 0.14 ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hsq : √(φ / (11 * N)) ≤ 0.14 := by
    rw [show (0.14 : ℝ) = √(0.14 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hq
  have hηR : η ≤ 0.14 * (ε * R) := by
    rw [hη_def, mul_comm (0.14 : ℝ)]; exact mul_le_mul_of_nonneg_left hsq hεR.le
  have hD4 := measureReal_exists_norm_add_sub_lt_le_of_separated S Λ hεR hη0 hηR hS
  set U : Set ℂ := {w | ∃ s ∈ S, ∃ a ∈ Λ, ‖s + w - a‖ < η}
  have hU : MeasurableSet U := by
    have : U = ⋃ s ∈ S, ⋃ a ∈ Λ, {w | ‖s + w - a‖ < η} := by ext; simp [U]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun s _ => Finset.measurableSet_biUnion _ fun a _ =>
      measurableSet_lt (by fun_prop) measurable_const
  have hmeas : Measurable (polarDisk 0 (ε * R)) := by unfold polarDisk; fun_prop
  have hpre : {x | ∃ s ∈ S, ∃ i, ‖s + polarDisk 0 (ε * R) x - e i‖ < η} =
      polarDisk 0 (ε * R) ⁻¹' U := by
    ext x; simp [U, Λ]
  rw [hpre, ← map_measureReal_apply hmeas hU, map_polarDisk_eq_diskUniform 0 hεR]
  refine hD4.trans ?_
  have hratio : (η / (ε * R)) ^ 2 = φ / (11 * N) := by
    rw [hη_def, mul_div_cancel_left₀ _ hεR.ne', Real.sq_sqrt hq0]
  rw [hratio]
  calc 11 * (Λ.card : ℝ) * (φ / (11 * N)) ≤ 11 * N * (φ / (11 * N)) := by gcongr
    _ = φ := by field_simp

/-! ### The program -/

open Ops

section Program

variable {O Q : Type} [Has ScalarOp O] [Has DiskSampleOp O]

/-- One exceptional shift from a net point: $\mathrm{fl}(z + \mathrm{fl}(\tilde R g))$
componentwise, for the radius word at `Rt`, the net point $g$ (a pair at `Gp`), the rounded
centre $z$ (a pair at `Z`) and one scratch word `T`. The interface is
`[] (Rt, Gp, Z, T) → (S)`. -/
def excShiftPoint : Impl O Q := opsImpl% [] (Rt, Gp, Z, T) → (S) {
  call (Has.inj ScalarOp.mul) [] (Rt, Gp) → (T);
  call (Has.inj ScalarOp.add) [] (Z, T) → (S);
  call (Has.inj ScalarOp.mul) [] (Rt, Gp[1]) → (T);
  call (Has.inj ScalarOp.add) [] (Z[1], T) → (S[1])
}

/-- The exceptional shifts with six caller-owned scratch words: the translate radius
$\mathrm{fl}(c_w\tilde R)$, the polar sample $w$ of that radius, the rounded centre
$\mathrm{fl}(r + w)$, and one product; then, for each of the $n_0$ stored net points $g_j$, the
shift $\mathrm{fl}(\mathrm{fl}(r + w) + \mathrm{fl}(\tilde R g_j))$ componentwise. The
interface is `[n0] (C, Rt, Cw, G, T) → (Ss)`. -/
def excShiftsWithScratch : Impl O Q := opsImpl% [n0] (C, Rt, Cw, G, T) → (Ss) {
  call (Has.inj ScalarOp.mul) [] (Cw, Rt) → (T);
  call (Has.inj DiskSampleOp.polar) [] (T) → (T[1]);
  call (Has.inj ScalarOp.add) [] (C, T[1]) → (T[3]);
  call (Has.inj ScalarOp.add) [] (C[1], T[2]) → (T[4]);
  for j < n0 {
    run excShiftPoint.body [] (Rt, G[2 * j], T[3], T[5], Ss[2 * j])
  }
}

/-- **The exceptional shifts** $\mathrm{Exc}$ ([BanksGarzaVargasSrivastava2022, Lemma 5.3]):
from the centre $r$ (a pair at `C`), the radius word $\tilde R$ at `Rt`, the translate factor
$c_w$ at `Cw` and $n_0$ net points $g_j$ (pairs at `G`, global data), draw one polar sample $w$
of radius $\mathrm{fl}(c_w\tilde R)$ and store the $n_0$ shifts
$\mathrm{fl}(r + w + \tilde R g_j)$ as pairs at `Ss`. The six scratch words are scoped. The
interface is `[n0] (C, Rt, Cw, G) → (Ss)`. -/
def excShifts : Impl O Q := opsImpl% [n0] (C, Rt, Cw, G) → (Ss) {
  let T ← alloc 6;
  run excShiftsWithScratch.body [n0] (C, Rt, Cw, G, T, Ss)
}

end Program

/-- The rounded centre $\mathrm{fl}(r + w)$ of the exceptional shifts, as a pair of words. -/
def excCentreWord (M : Machine ℝ) (r w : ℂ) : ℝ × ℝ := (M.add r.re w.re, M.add r.im w.im)

/-- The computed exceptional shift $\mathrm{fl}(z + \mathrm{fl}(Rg))$ componentwise, from the
rounded centre `z`, the radius word `R` and the net point `g`. -/
def excShiftWord (M : Machine ℝ) (z : ℝ × ℝ) (R : ℝ) (g : ℂ) : ℂ :=
  ⟨M.add z.1 (M.mul R g.re), M.add z.2 (M.mul R g.im)⟩

section Program

variable {O Q : Type} [Has ScalarOp O] [Has DiskSampleOp O]

omit [Has DiskSampleOp O] in
/-- One exceptional shift on any scalar machine stores `NLAlib.ShiftedQR.excShiftWord`. The
output pair and the scratch word are disjoint from each other and from the inputs. -/
private theorem excShiftPoint_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {m : Mem ℝ} {rt gp zt tt sp : ℕ × ℕ} {z : ℝ × ℝ} {R : ℝ} {gv : ℂ}
    (hrt : m.store.get rt.1 rt.2 = some R)
    (hg1 : m.store.get gp.1 gp.2 = some gv.re) (hg2 : m.store.get gp.1 (gp.2 + 1) = some gv.im)
    (hz1 : m.store.get zt.1 zt.2 = some z.1) (hz2 : m.store.get zt.1 (zt.2 + 1) = some z.2)
    (htt : tt.2 < m.store.len tt.1) (hsp : sp.2 + 2 ≤ m.store.len sp.1)
    (htr : Fp.Disj (Store.inBlock tt.1 tt.2 1) (Store.inBlock rt.1 rt.2 1))
    (htg : Fp.Disj (Store.inBlock tt.1 tt.2 1) (Store.inBlock gp.1 gp.2 2))
    (htz : Fp.Disj (Store.inBlock tt.1 tt.2 1) (Store.inBlock zt.1 zt.2 2))
    (hts : Fp.Disj (Store.inBlock tt.1 tt.2 1) (Store.inBlock sp.1 sp.2 2))
    (hsr : Fp.Disj (Store.inBlock sp.1 sp.2 2) (Store.inBlock rt.1 rt.2 1))
    (hsg : Fp.Disj (Store.inBlock sp.1 sp.2 2) (Store.inBlock gp.1 gp.2 2))
    (hsz : Fp.Disj (Store.inBlock sp.1 sp.2 2) (Store.inBlock zt.1 zt.2 2)) :
    Writes .total I τ (excShiftPoint (O := O) (Q := Q)).body (Env.frame [] [rt, gp, zt, tt, sp])
      (Store.inBlock sp.1 sp.2 2 ⊔ Store.inBlock tt.1 tt.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get sp.1 sp.2 = some (excShiftWord M z R gv).re ∧
        m'.store.get sp.1 (sp.2 + 1) = some (excShiftWord M z R gv).im) m := by
  have hrl := Store.lt_length_of_get hrt
  have hgl := Store.lt_length_of_get hg1
  have hzl := Store.lt_length_of_get hz1
  have htl := Store.lt_length_of_lt_len htt
  have hsl := Store.lt_length_of_lt_len (show sp.2 < m.store.len sp.1 by omega)
  unfold excShiftPoint
  refine (writes_call_bin (hS .mul) rfl rfl trivial hrt hg1 rfl
    (fun _ => ⟨by room, by room⟩)).seq_le (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, hT₁⟩
  have hz1₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (htz.mono le_rfl (by fp_sub)) hz1
  refine (writes_call_bin (hS .add) rfl rfl trivial hz1₁ hT₁ rfl
    (fun _ => ⟨by room, by room⟩)).seq_le (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, hS₂⟩
  have hrt₁ := hfr₁.keep (Store.readsOnly_get _ _ _) htr hrt
  have hg2₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (htg.mono le_rfl (by fp_sub)) hg2
  have hz2₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (htz.mono le_rfl (by fp_sub)) hz2
  have hrt₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (hsr.mono (by fp_sub) le_rfl) hrt₁
  have hg2₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (hsg.mono (by fp_sub) (by fp_sub)) hg2₁
  have hz2₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (hsz.mono (by fp_sub) (by fp_sub)) hz2₁
  refine (writes_call_bin (hS .mul) rfl rfl trivial hrt₂ hg2₂ rfl
    (fun _ => ⟨by room, by room⟩)).seq_le (by fp_sub) ?_
  intro m₃ hfr₃ ⟨hp₃, hT₃⟩
  have hz2₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (htz.mono le_rfl (by fp_sub)) hz2₂
  have hS₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (hts.mono le_rfl (by fp_sub)) hS₂
  refine (writes_call_bin (hS .add) rfl rfl trivial hz2₃ hT₃ rfl
    (fun _ => ⟨by room, by room⟩)).mono (by fp_sub) ?_
  intro m₄ hfr₄ ⟨hp₄, hS₄⟩
  refine ⟨hp₄.trans (hp₃.trans (hp₂.trans hp₁)), ?_, hS₄⟩
  exact hfr₄.keep (Store.readsOnly_get _ _ _) (by disjoint) hS₃

omit [Has DiskSampleOp O] in
/-- The loop of `NLAlib.ShiftedQR.excShiftsWithScratch` on any scalar machine stores the computed
shifts of the net points, with the rounded centre in `T[3]`, `T[4]`. -/
private theorem excShiftsLoop_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {m : Mem ℝ} {c rt cw g t ss : ℕ × ℕ} {z : ℝ × ℝ} {R : ℝ} {gs : List ℂ}
    (hrt : m.store.get rt.1 rt.2 = some R)
    (hg : m.store.readBlock g.1 g.2 (2 * gs.length) = some (gs.flatMap fun z => [z.re, z.im]))
    (hz1 : m.store.get t.1 (t.2 + 3) = some z.1) (hz2 : m.store.get t.1 (t.2 + 4) = some z.2)
    (ht : t.2 + 6 ≤ m.store.len t.1) (hss : ss.2 + 2 * gs.length ≤ m.store.len ss.1)
    (htr : Fp.Disj (Store.inBlock t.1 t.2 6) (Store.inBlock rt.1 rt.2 1))
    (htg : Fp.Disj (Store.inBlock t.1 t.2 6) (Store.inBlock g.1 g.2 (2 * gs.length)))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 6) (Store.inBlock ss.1 ss.2 (2 * gs.length)))
    (hsr : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * gs.length)) (Store.inBlock rt.1 rt.2 1))
    (hsg : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * gs.length))
      (Store.inBlock g.1 g.2 (2 * gs.length))) :
    Writes .total I τ (.loop (.var 0)
      (.frame [] [⟨1, .var 2⟩, ⟨3, .var 4 + .const 2 * .var 7⟩, ⟨4, .var 5 + .const 3⟩,
        ⟨4, .var 5 + .const 5⟩, ⟨5, .var 6 + .const 2 * .var 7⟩]
        (excShiftPoint (O := O) (Q := Q)).body))
      (Env.frame [gs.length] [c, rt, cw, g, t, ss])
      (Store.inBlock ss.1 ss.2 (2 * gs.length) ⊔ Store.inBlock t.1 (t.2 + 5) 1)
      (fun m' => m'.pos = m.pos ∧ ∀ j < gs.length,
        m'.store.get ss.1 (ss.2 + 2 * j) = some (excShiftWord M z R (gs.getD j 0)).re ∧
        m'.store.get ss.1 (ss.2 + 2 * j + 1) = some (excShiftWord M z R (gs.getD j 0)).im) m := by
  have hrl := Store.lt_length_of_get hrt
  have hgl := Store.lt_length_of_get hz1
  refine writes_loop_disjoint_prefix_scratch (fun j => Store.inBlock ss.1 (ss.2 + 2 * j) 2)
    (fun j st => st.get ss.1 (ss.2 + 2 * j) = some (excShiftWord M z R (gs.getD j 0)).re ∧
      st.get ss.1 (ss.2 + 2 * j + 1) = some (excShiftWord M z R (gs.getD j 0)).im)
    rfl (fun j hj => le_sup_of_le_left (Fp.inBlock_le_inBlock (by omega) (by omega)))
    le_sup_right (fun i _ j _ hij => by disjoint)
    (fun j hj => (hts.symm.mono (Fp.inBlock_le_inBlock (by omega) (by omega))
      (Fp.inBlock_le_inBlock (by omega) (by omega))).symm)
    (fun j _ => ((Store.readsOnly_get _ _ _).and (Store.readsOnly_get _ _ _)).mono
      (by fp_sub)) ?_
  intro j hj m' hfr
  have hsl := Store.lt_length_of_lt_len (show ss.2 < m.store.len ss.1 by omega)
  have hpre : Fp.loopPrefix (fun j => Store.inBlock ss.1 (ss.2 + 2 * j) 2) j ⊔
      Store.inBlock t.1 (t.2 + 5) 1 ≤
        Store.inBlock ss.1 ss.2 (2 * gs.length) ⊔ Store.inBlock t.1 (t.2 + 5) 1 :=
    sup_le_sup (fun b x ⟨i, hi, hx⟩ => Fp.inBlock_le_inBlock (by omega) (by omega) b x hx) le_rfl
  have hfr' := hfr.mono hpre
  have hjg : 2 * j + 1 < 2 * gs.length := by omega
  obtain ⟨hg1, hg2⟩ := get_of_readBlock_flatMap_pair hg hj
  have hD := fun (F : Fp) (h₁ : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * gs.length)) F)
      (h₂ : Fp.Disj (Store.inBlock t.1 (t.2 + 5) 1) F) =>
    (Fp.disj_sup_left.mpr ⟨h₁, h₂⟩ : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * gs.length) ⊔
      Store.inBlock t.1 (t.2 + 5) 1) F)
  have hrt' := hfr'.keep (Store.readsOnly_get _ _ _)
    (hD _ hsr (htr.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl)) hrt
  have hg1' := hfr'.keep (Store.readsOnly_get _ _ _) (hD _
    (hsg.mono le_rfl (Fp.inBlock_le_inBlock (by omega) (by omega)))
    (htg.mono (Fp.inBlock_le_inBlock (by omega) (by omega))
      (Fp.inBlock_le_inBlock (by omega) (by omega)))) hg1
  have hg2' := hfr'.keep (Store.readsOnly_get _ _ _) (hD _
    (hsg.mono le_rfl (Fp.inBlock_le_inBlock (by omega) (by omega)))
    (htg.mono (Fp.inBlock_le_inBlock (by omega) (by omega))
      (Fp.inBlock_le_inBlock (by omega) (by omega)))) hg2
  have hz1' := hfr'.keep (Store.readsOnly_get _ _ _) (hD _
    (hts.symm.mono le_rfl (Fp.inBlock_le_inBlock (by omega) (by omega))) (by disjoint)) hz1
  have hz2' := hfr'.keep (Store.readsOnly_get _ _ _) (hD _
    (hts.symm.mono le_rfl (Fp.inBlock_le_inBlock (by omega) (by omega))) (by disjoint)) hz2
  have hgj : gs.getD j 0 = gs[j] := by simp [List.getD_eq_getElem?_getD, hj]
  rw [hgj]
  refine ((excShiftPoint_writes_word (τ := τ) (z := z) (rt := rt) (gp := (g.1, g.2 + 2 * j))
    (zt := (t.1, t.2 + 3)) (tt := (t.1, t.2 + 5)) (sp := (ss.1, ss.2 + 2 * j)) hS hrt' hg1'
    (by simpa [Nat.add_assoc] using hg2') hz1' hz2' (by dsimp only; rw [hfr.len_eq]; omega)
    (by dsimp only; rw [hfr.len_eq]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_).in_frame rfl
      (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval]) ?_).mono
      (by fp_sub) fun m'' _ h => ⟨h.1, h.2.1, by simpa [Nat.add_assoc] using h.2.2⟩
  · exact htr.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl
  · exact htg.mono (Fp.inBlock_le_inBlock (by omega) (by omega))
      (Fp.inBlock_le_inBlock (by omega) (by omega))
  · disjoint
  · exact hts.mono (Fp.inBlock_le_inBlock (by omega) (by omega))
      (Fp.inBlock_le_inBlock (by omega) (by omega))
  · exact hsr.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl
  · exact hsg.mono (Fp.inBlock_le_inBlock (by omega) (by omega))
      (Fp.inBlock_le_inBlock (by omega) (by omega))
  · exact hts.symm.mono (Fp.inBlock_le_inBlock (by omega) (by omega))
      (Fp.inBlock_le_inBlock (by omega) (by omega))
  · have hlen := hfr.length_eq
    have hgl' := Store.lt_length_of_get hg1
    simp [Mem.Live, hlen, hrl, hgl, hgl', hsl]

/-- The polar sample drawn by `NLAlib.ShiftedQR.excShifts` from the tape `τ` at the position
`p`, with the radius word `ρ`. -/
noncomputable def excSample (τ : Tape ℝ) (s p : ℕ) (ρ : ℝ) : ℂ :=
  polarDisk 0 ρ (Tape.windowFn τ s p 2)

/-- `NLAlib.ShiftedQR.excShiftsWithScratch` on any scalar machine with an exact polar sampler
stores the computed shifts `NLAlib.ShiftedQR.excShiftWord` of the net points, for the sample of
radius $\mathrm{fl}(c_w\tilde R)$ read at the start position, and advances the position by
two. -/
private theorem excShiftsWithScratch_writes_word {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) {s : ℕ} (hD : IsPolarDiskSampler s I) {τ : Tape ℝ} {m : Mem ℝ}
    {c rt cw g t ss : ℕ × ℕ} {r : ℂ} {R cv : ℝ} {gs : List ℂ}
    (hcr : m.store.get c.1 c.2 = some r.re) (hci : m.store.get c.1 (c.2 + 1) = some r.im)
    (hrt : m.store.get rt.1 rt.2 = some R) (hcw : m.store.get cw.1 cw.2 = some cv)
    (hg : m.store.readBlock g.1 g.2 (2 * gs.length) = some (gs.flatMap fun z => [z.re, z.im]))
    (ht : t.2 + 6 ≤ m.store.len t.1) (hss : ss.2 + 2 * gs.length ≤ m.store.len ss.1)
    (htc : Fp.Disj (Store.inBlock t.1 t.2 6) (Store.inBlock c.1 c.2 2))
    (htr : Fp.Disj (Store.inBlock t.1 t.2 6) (Store.inBlock rt.1 rt.2 1))
    (htg : Fp.Disj (Store.inBlock t.1 t.2 6) (Store.inBlock g.1 g.2 (2 * gs.length)))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 6) (Store.inBlock ss.1 ss.2 (2 * gs.length)))
    (hsr : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * gs.length)) (Store.inBlock rt.1 rt.2 1))
    (hsg : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * gs.length))
      (Store.inBlock g.1 g.2 (2 * gs.length))) :
    Writes .total I τ (excShiftsWithScratch (O := O) (Q := Q)).body
      (Env.frame [gs.length] [c, rt, cw, g, t, ss])
      (Store.inBlock ss.1 ss.2 (2 * gs.length) ⊔ Store.inBlock t.1 t.2 6)
      (fun m' => m'.pos = m.pos + 2 ∧ m'.store.readBlock ss.1 ss.2 (2 * gs.length) =
        some ((gs.map (excShiftWord M (excCentreWord M r (excSample τ s m.pos (M.mul cv R)))
          R)).flatMap fun z => [z.re, z.im])) m := by
  have hrl := Store.lt_length_of_get hrt
  have hcl := Store.lt_length_of_get hcr
  have htl := Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by omega)
  have hwl := Store.lt_length_of_get hcw
  unfold excShiftsWithScratch
  refine (writes_call_bin (hS .mul) rfl rfl trivial hcw hrt rfl
    (fun _ => ⟨by room, by room⟩)).seq_le (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, hT₁⟩
  set W := excSample τ s m.pos (M.mul cv R) with hW_def
  have hread : m₁.readBlocks [t] [1] = some [[M.mul cv R]] := by
    simp [Mem.readBlocks, Store.readBlock, hT₁]
  refine (writes_call (R := polarDiskRel s) hD (d := []) (a := [t]) (b := [(t.1, t.2 + 1)])
    (k := 2) (ls := [2]) rfl rfl rfl rfl rfl rfl trivial (by simp [Fp.Apart])
    (fun _ => ⟨by room, ⟨_, hread, trivial⟩, by
      simp [Mem.Room, hfr₁.len_eq]; omega⟩)).seq_le (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨hp₂, xs, ys, hr, hys, hrel⟩
  have hxs : xs = [[M.mul cv R]] := Option.some.inj (hr.symm.trans hread)
  have hwin : (fun j : Fin 2 => (τ.window s m₁.pos 2).getD j 0) = Tape.windowFn τ s m.pos 2 := by
    funext j
    fin_cases j <;> simp [Tape.window, Tape.windowFn, List.getD_eq_getElem?_getD, hp₁]
  have hys' := hrel (M.mul cv R) hxs
  simp only [polarDiskRel] at hys'
  rw [hwin] at hys'
  have hWb : m₂.store.readBlock t.1 (t.2 + 1) 2 = some [W.re, W.im] := by
    subst hys'
    obtain ⟨y, hy, hyy⟩ := Option.bind_eq_some_iff.mp (by simpa [Mem.readBlocks] using hys)
    simp only [Option.some.injEq, List.cons.injEq, and_true] at hyy
    rw [hy, hyy]; rfl
  have hW1 := Store.get_of_readBlock hWb (j := 0) (by norm_num) 0
  have hW2 := Store.get_of_readBlock hWb (j := 1) (by norm_num) 0
  simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at hW1 hW2
  have hD₁₂ : ∀ {F : Fp}, Fp.Disj (Store.inBlock t.1 t.2 6) F →
      Fp.Disj (Store.inBlock t.1 t.2 1) F ∧ Fp.Disj (Fp.blocks [(t.1, t.2 + 1)] [2]) F :=
    fun h => ⟨h.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl,
      h.mono (sup_le (Fp.inBlock_le_inBlock (by omega) (by omega)) bot_le) le_rfl⟩
  have hcr₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (hD₁₂ (htc.mono le_rfl (by fp_sub))).2
    (hfr₁.keep (Store.readsOnly_get _ _ _) (hD₁₂ (htc.mono le_rfl (by fp_sub))).1 hcr)
  have hci₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (hD₁₂ (htc.mono le_rfl (by fp_sub))).2
    (hfr₁.keep (Store.readsOnly_get _ _ _) (hD₁₂ (htc.mono le_rfl (by fp_sub))).1 hci)
  have hrt₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (hD₁₂ htr).2
    (hfr₁.keep (Store.readsOnly_get _ _ _) (hD₁₂ htr).1 hrt)
  have hg₂ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) (hD₁₂ htg).2
    (hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (hD₁₂ htg).1 hg)
  refine (writes_call_bin (hS .add) rfl rfl trivial hcr₂ hW1 rfl
    (fun _ => ⟨by room, by room⟩)).seq_le (by fp_sub) ?_
  intro m₃ hfr₃ ⟨hp₃, hZ₃⟩
  have hD₃ : ∀ {F : Fp}, Fp.Disj (Store.inBlock t.1 t.2 6) F →
      Fp.Disj (Store.inBlock t.1 (t.2 + 3) 1) F :=
    fun h => h.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl
  have hci₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (hD₃ (htc.mono le_rfl (by fp_sub))) hci₂
  have hW2₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (by disjoint) hW2
  refine (writes_call_bin (hS .add) rfl rfl trivial hci₃ hW2₃ rfl
    (fun _ => ⟨by room, by room⟩)).seq_le (by fp_sub) ?_
  intro m₄ hfr₄ ⟨hp₄, hZ₄⟩
  have hD₄ : ∀ {F : Fp}, Fp.Disj (Store.inBlock t.1 t.2 6) F →
      Fp.Disj (Store.inBlock t.1 (t.2 + 4) 1) F :=
    fun h => h.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl
  have hZ₃' := hfr₄.keep (Store.readsOnly_get _ _ _) (by disjoint) hZ₃
  have hrt₄ := hfr₄.keep (Store.readsOnly_get _ _ _) (hD₄ htr)
    (hfr₃.keep (Store.readsOnly_get _ _ _) (hD₃ htr) hrt₂)
  have hg₄ := hfr₄.keep (Store.readsOnly_readBlock _ _ _ _) (hD₄ htg)
    (hfr₃.keep (Store.readsOnly_readBlock _ _ _ _) (hD₃ htg) hg₂)
  have hlen : ∀ b, m₄.store.len b = m.store.len b := fun b => by
    rw [hfr₄.len_eq, hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]
  refine (excShiftsLoop_writes_word (τ := τ) (c := c) (cw := cw)
    (z := excCentreWord M r W) hS hrt₄ hg₄ hZ₃' hZ₄ (by rw [hlen]; exact ht)
    (by rw [hlen]; exact hss) htr htg hts hsr hsg).mono (by fp_sub) ?_
  intro m₅ _ ⟨hp₅, hcells⟩
  refine ⟨by rw [hp₅, hp₄, hp₃, hp₂, hp₁], ?_⟩
  have h := readBlock_flatMap_pair_of_get (s := m₅.store) (b := ss.1) (o := ss.2)
    (zs := gs.map (excShiftWord M (excCentreWord M r W) R)) fun j hj => ?_
  · simpa using h
  simp only [List.length_map] at hj
  have hgj : gs.getD j 0 = gs[j] := by simp [List.getD_eq_getElem?_getD, hj]
  have h := hcells j hj
  rw [hgj] at h
  simpa using h
/-- **The exceptional shifts on any scalar machine** with an exact polar sampler on the stream
`s`: `NLAlib.ShiftedQR.excShifts` writes only its output, stores the computed shifts
`NLAlib.ShiftedQR.excShiftWord` of the $n_0$ net points for the polar sample of radius
$\mathrm{fl}(c_w\tilde R)$ read at the start position, and advances the position by two. The
output is disjoint from the radius word and the net. -/
theorem excShifts_writes_word {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) {s : ℕ} (hD : IsPolarDiskSampler s I) {τ : Tape ℝ} {m : Mem ℝ}
    {c rt cw g ss : ℕ × ℕ} {r : ℂ} {R cv : ℝ} {gs : List ℂ}
    (hcr : m.store.get c.1 c.2 = some r.re) (hci : m.store.get c.1 (c.2 + 1) = some r.im)
    (hrt : m.store.get rt.1 rt.2 = some R) (hcw : m.store.get cw.1 cw.2 = some cv)
    (hg : m.store.readBlock g.1 g.2 (2 * gs.length) = some (gs.flatMap fun z => [z.re, z.im]))
    (hss : ss.2 + 2 * gs.length ≤ m.store.len ss.1) (hl : m.Live [c, rt, cw, g, ss])
    (hsr : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * gs.length)) (Store.inBlock rt.1 rt.2 1))
    (hsg : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * gs.length))
      (Store.inBlock g.1 g.2 (2 * gs.length))) :
    Writes .total I τ (excShifts (O := O) (Q := Q)).body
      (Env.frame [gs.length] [c, rt, cw, g, ss]) (Store.inBlock ss.1 ss.2 (2 * gs.length))
      (fun m' => m'.pos = m.pos + 2 ∧ m'.store.readBlock ss.1 ss.2 (2 * gs.length) =
        some ((gs.map (excShiftWord M (excCentreWord M r (excSample τ s m.pos (M.mul cv R)))
          R)).flatMap fun z => [z.re, z.im])) m := by
  obtain ⟨hcl, hrl, hwl, hgl, hsl⟩ : c.1 < m.store.length ∧ rt.1 < m.store.length ∧
      cw.1 < m.store.length ∧ g.1 < m.store.length ∧ ss.1 < m.store.length := by
    simpa [Mem.Live] using hl
  change Writes .total I τ (Stmt.allocs [.const 6] _) _ _ _ m
  refine writes_allocs_readBlock_at rfl hsl ?_
  intro store hlen hlens hBelow
  let t : ℕ × ℕ := (m.store.length, 0)
  have ht : store.len t.1 = 6 := by simpa [t] using hlens 0 (by simp)
  have hg' : store.readBlock g.1 g.2 (2 * gs.length) = some (gs.flatMap fun z => [z.re, z.im]) :=
    hBelow.readBlock_of hgl hg
  have hdt : ∀ {o n : ℕ} {b : ℕ × ℕ}, b.1 < m.store.length →
      Fp.Disj (Store.inBlock t.1 t.2 6) (Store.inBlock b.1 o n) := fun h =>
    Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have hbody := excShiftsWithScratch_writes_word (τ := τ) (m := ⟨store, m.pos⟩) (t := t)
    (c := c) (rt := rt) (cw := cw) (g := g) (ss := ss) hS hD
    (hBelow.get_of hcl hcr) (hBelow.get_of hcl hci) (hBelow.get_of hrl hrt)
    (hBelow.get_of hwl hcw) hg' (by simp [t] at ht ⊢; omega)
    (by rw [(hBelow ss.1 hsl).1]; exact hss) (hdt hcl) (hdt hrl)
    (hdt hgl) (hdt hsl) hsr hsg
  exact (hbody.in_frame rfl rfl (by simp [Mem.Live, t, hlen]; omega)).mono
    (sup_le le_sup_left (Fp.inBlock_le_sup_above le_rfl)) (fun _ _ h => h)

end Program

/-! ### The mathematics of the computed shifts -/

/-- **The rounding error of one computed exceptional shift**: under the standard model with
$0 \le \boldsymbol{u} \le 1$, the shift $\mathrm{fl}(\mathrm{fl}(r + w) + \mathrm{fl}(Rg))$,
componentwise, is within $6\boldsymbol{u}(\lvert r\rvert + \lvert w\rvert + \lvert R\rvert
\lvert g\rvert)$ of $r + w + Rg$. -/
theorem norm_excShiftWord_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu1 : u ≤ 1)
    (r w : ℂ) (R : ℝ) (g : ℂ) :
    ‖excShiftWord M (excCentreWord M r w) R g - (r + w + R * g)‖ ≤
      6 * u * (‖r‖ + ‖w‖ + |R| * ‖g‖) := by
  have hu0 := hM.roundoff_nonneg
  have comp : ∀ a x y : ℝ, |a + x| ≤ ‖r‖ + ‖w‖ → |y| ≤ ‖g‖ →
      |M.add (M.add a x) (M.mul R y) - (a + x + R * y)| ≤
        3 * u * (‖r‖ + ‖w‖ + |R| * ‖g‖) := by
    intro a x y hA hB
    have h1 := hM.add a x
    have h2 := hM.mul R y
    have h3 := hM.add (M.add a x) (M.mul R y)
    simp only [id] at h1 h2 h3
    have hRy : |R * y| ≤ |R| * ‖g‖ := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hB (abs_nonneg R)
    set A := a + x
    set B := R * y
    have e1 : |M.add a x + M.mul R y| ≤ (1 + u) * (|A| + |B|) := by
      have := abs_add_le (M.add a x - A) (M.mul R y - B)
      have := abs_add_le A B
      calc |M.add a x + M.mul R y| = |(M.add a x - A) + (M.mul R y - B) + (A + B)| := by ring_nf
        _ ≤ |M.add a x - A| + |M.mul R y - B| + |A + B| := abs_add_three _ _ _
        _ ≤ u * |A| + u * |B| + (|A| + |B|) := by gcongr
        _ = (1 + u) * (|A| + |B|) := by ring
    calc |M.add (M.add a x) (M.mul R y) - (A + B)|
        = |(M.add (M.add a x) (M.mul R y) - (M.add a x + M.mul R y)) + (M.add a x - A) +
            (M.mul R y - B)| := by ring_nf
      _ ≤ |M.add (M.add a x) (M.mul R y) - (M.add a x + M.mul R y)| + |M.add a x - A| +
            |M.mul R y - B| := abs_add_three _ _ _
      _ ≤ u * ((1 + u) * (|A| + |B|)) + u * |A| + u * |B| := by
          gcongr
          exact h3.trans (mul_le_mul_of_nonneg_left e1 hu0)
      _ = (2 * u + u ^ 2) * (|A| + |B|) := by ring
      _ ≤ 3 * u * (|A| + |B|) := by gcongr; nlinarith
      _ ≤ 3 * u * (‖r‖ + ‖w‖ + |R| * ‖g‖) := by gcongr
  have hre := comp r.re w.re g.re ((abs_add_le _ _).trans
    (add_le_add (Complex.abs_re_le_norm r) (Complex.abs_re_le_norm w)))
    (Complex.abs_re_le_norm g)
  have him := comp r.im w.im g.im ((abs_add_le _ _).trans
    (add_le_add (Complex.abs_im_le_norm r) (Complex.abs_im_le_norm w)))
    (Complex.abs_im_le_norm g)
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e : (excShiftWord M (excCentreWord M r w) R g - (r + w + R * g)).re =
      M.add (M.add r.re w.re) (M.mul R g.re) - (r.re + w.re + R * g.re) := by
    simp [excShiftWord, excCentreWord]
  have e' : (excShiftWord M (excCentreWord M r w) R g - (r + w + R * g)).im =
      M.add (M.add r.im w.im) (M.mul R g.im) - (r.im + w.im + R * g.im) := by
    simp [excShiftWord, excCentreWord]
  rw [e, e']
  linarith

/-- A polar sample from the unit square lies in the disk of its radius. -/
theorem norm_polarDisk_le {ρ : ℝ} (hρ : 0 ≤ ρ) {x : Fin 2 → ℝ} (hx : ∀ j, x j ∈ Set.Icc 0 1) :
    ‖polarDisk 0 ρ x‖ ≤ ρ := by
  have h1 : √(x 0) ≤ 1 := Real.sqrt_le_one.mpr (hx 0).2
  rw [polarDisk, zero_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [Real.sqrt_nonneg (x 0)]

/-- The count of the net of `NLAlib.ShiftedQR.excShifts`: for $0 < \varepsilon \le 1/2$ the
square grid of spacing parameter $3\varepsilon/4$ has at most $9/\varepsilon^2$ points. -/
private theorem length_squareGrid_three_quarter_le (c : ℂ) (R : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) : ((squareGrid c R (3 * ε / 4)).length : ℝ) ≤ 9 / ε ^ 2 := by
  have h := length_squareGrid_mul_sq_le c R (ε := 3 * ε / 4) (by positivity)
  have hs : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 := Real.sqrt_nonneg 2
  set L := ((squareGrid c R (3 * ε / 4)).length : ℝ)
  rw [le_div_iff₀ (by positivity)]
  have h2 : (Real.sqrt 2 + 2 * (3 * ε / 4)) ^ 2 ≤ 2.25 ^ 2 := by
    apply pow_le_pow_left₀ (by positivity); linarith
  nlinarith

/-- The computed shifts of a net point lie within $6\boldsymbol{u}(\lvert r\rvert + 3\tilde R)$
of the translated grid point. -/
private theorem norm_excShiftWord_sub_le_of_mem {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu : u ≤ 1 / 100) {r W g : ℂ} {R ε ρw : ℝ} (hR : 0 < R) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hρhi : ρw ≤ (1 + u) * (ε / 2 * R)) (hW : ‖W‖ ≤ ρw)
    (hg : g ∈ squareGrid 0 1.3 (3 * ε / 4)) :
    ‖excShiftWord M (excCentreWord M r W) R g - (r + R * g + W)‖ ≤ 6 * u * (‖r‖ + 3 * R) ∧
      ‖g‖ ≤ 1.84 := by
  have hu0 := hM.roundoff_nonneg
  have hg' : ‖g‖ ≤ 1.84 := by
    have := norm_sub_le_of_mem_squareGrid (by norm_num) (by positivity) hg
    rw [sub_zero] at this
    have hs : Real.sqrt 2 < 1.4143 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  refine ⟨?_, hg'⟩
  have h := norm_excShiftWord_sub_le hM (by linarith) r W R g
  rw [show r + W + (R : ℂ) * g = r + R * g + W by ring, abs_of_pos hR] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have h1 : (1 + u) ≤ 1.01 := by linarith
  have h2 : ε / 2 * R ≤ 1 / 4 * R := by nlinarith
  have : ρw ≤ 0.26 * R := by
    calc ρw ≤ (1 + u) * (ε / 2 * R) := hρhi
      _ ≤ 1.01 * (1 / 4 * R) := mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ ≤ 0.26 * R := by nlinarith
  nlinarith [norm_nonneg g]

/-- **The computed exceptional shifts from a good translate**: let $0 < \varepsilon \le 1/2$,
$\tilde R > 0$, $0 \le \boldsymbol{u} \le 1/100$ (standard model), the translate radius
$\rho_w$ within $\boldsymbol{u}$ of $\varepsilon\tilde R/2$, $\lvert w\rvert \le \rho_w$, every
translated grid point $r + \tilde R g + w$ at distance at least $\rho_w\sqrt q$ from every
$\lambda_i$, and the rounding $6\boldsymbol{u}(\lvert r\rvert + 3\tilde R)$ at most
$0.005\,\varepsilon\tilde R$ and at most $\varepsilon\tilde R\sqrt q/8$. Then the computed
shifts are at most $9/\varepsilon^2$, cover $\mathbb{D}(r, \tilde R)$ at radius
$\varepsilon\tilde R$, keep the distance $\varepsilon\tilde R\sqrt q/4$ from every $\lambda_i$,
and lie in $\mathbb{D}(r, 2.1\tilde R)$. -/
private theorem excShifts_props {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) {N : ℕ}
    (e : Fin N → ℂ) {r W : ℂ} {R ε ρw q : ℝ} (hR : 0 < R) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hu : u ≤ 1 / 100) (hρlo : (1 - u) * (ε / 2 * R) ≤ ρw)
    (hρhi : ρw ≤ (1 + u) * (ε / 2 * R)) (hW : ‖W‖ ≤ ρw)
    (hgood : ∀ p ∈ squareGrid r (R * 1.3) (3 * ε / 4), ∀ i, ρw * √q ≤ ‖p + W - e i‖)
    (hδ : 6 * u * (‖r‖ + 3 * R) ≤ 0.005 * ε * R)
    (hδη : 6 * u * (‖r‖ + 3 * R) ≤ ε * R * √q / 8) :
    (((squareGrid 0 1.3 (3 * ε / 4)).map (excShiftWord M (excCentreWord M r W) R)).length : ℝ)
        ≤ 9 / ε ^ 2 ∧
      (∀ z : ℂ, ‖z - r‖ ≤ R → ∃ s ∈ (squareGrid 0 1.3 (3 * ε / 4)).map
        (excShiftWord M (excCentreWord M r W) R), ‖z - s‖ ≤ ε * R) ∧
      (∀ s ∈ (squareGrid 0 1.3 (3 * ε / 4)).map (excShiftWord M (excCentreWord M r W) R),
        ∀ i, ε * R * √q / 4 ≤ ‖e i - s‖) ∧
      ∀ s ∈ (squareGrid 0 1.3 (3 * ε / 4)).map (excShiftWord M (excCentreWord M r W) R),
        ‖s - r‖ ≤ 2.1 * R := by
  have hu0 := hM.roundoff_nonneg
  have hgrid := squareGrid_mul_eq_map r R 1.3 (3 * ε / 4)
  have herr := fun {g} (hg : g ∈ squareGrid 0 1.3 (3 * ε / 4)) =>
    norm_excShiftWord_sub_le_of_mem (r := r) hM hu hR hε hε2 hρhi hW hg
  refine ⟨by rw [List.length_map]; exact length_squareGrid_three_quarter_le 0 1.3 hε hε2,
    fun z hz => ?_, fun s hs i => ?_, fun s hs => ?_⟩
  · have hzW : ‖(z - W) - r‖ ≤ R * 1.3 := by
      calc ‖(z - W) - r‖ = ‖(z - r) - W‖ := by ring_nf
        _ ≤ ‖z - r‖ + ‖W‖ := norm_sub_le _ _
        _ ≤ R * 1.3 := by nlinarith
    obtain ⟨p, hp, hpz⟩ := exists_mem_squareGrid_norm_sub_le (by positivity)
      (by positivity : (0 : ℝ) < 3 * ε / 4) hzW
    rw [hgrid, List.mem_map] at hp
    obtain ⟨g, hg, rfl⟩ := hp
    refine ⟨_, List.mem_map_of_mem hg, ?_⟩
    calc ‖z - excShiftWord M (excCentreWord M r W) R g‖
        = ‖((z - W) - (r + R * g)) - (excShiftWord M (excCentreWord M r W) R g -
            (r + R * g + W))‖ := by ring_nf
      _ ≤ ‖(z - W) - (r + R * g)‖ + ‖excShiftWord M (excCentreWord M r W) R g -
            (r + R * g + W)‖ := norm_sub_le _ _
      _ ≤ 3 * ε / 4 * (R * 1.3) + 0.005 * ε * R := add_le_add hpz ((herr hg).1.trans hδ)
      _ ≤ ε * R := by nlinarith
  · rw [List.mem_map] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    have hp : r + R * g ∈ squareGrid r (R * 1.3) (3 * ε / 4) := by
      rw [hgrid]; exact List.mem_map_of_mem hg
    have h1 := hgood _ hp i
    have hsq : 0 ≤ √q := Real.sqrt_nonneg q
    have hA : 0 ≤ ε / 2 * R * √q := by positivity
    have hB : 0.99 * (ε / 2 * R * √q) ≤ ρw * √q := by
      nlinarith [mul_le_mul_of_nonneg_right hρlo hsq]
    set sv := excShiftWord M (excCentreWord M r W) R g
    have h3 := norm_sub_le_norm_sub_add_norm_sub (r + R * g + W) sv (e i)
    rw [norm_sub_rev (r + R * g + W) sv, norm_sub_rev sv (e i)] at h3
    linarith [(herr hg).1]
  · rw [List.mem_map] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    obtain ⟨h1, h2⟩ := herr hg
    have hRg : ‖(R : ℂ) * g‖ ≤ 1.84 * R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]; nlinarith [norm_nonneg g]
    calc ‖excShiftWord M (excCentreWord M r W) R g - r‖
        = ‖(excShiftWord M (excCentreWord M r W) R g - (r + R * g + W)) + (R * g) + W‖ := by
          ring_nf
      _ ≤ ‖excShiftWord M (excCentreWord M r W) R g - (r + R * g + W)‖ + ‖(R : ℂ) * g‖ + ‖W‖ :=
          norm_add₃_le
      _ ≤ 2.1 * R := by nlinarith

/-- **The net of the exceptional shifts**: the square grid of radius $1.3$ and spacing parameter
$3\varepsilon/4$ around $0$ (`NLAlib.squareGrid`), global data of `NLAlib.ShiftedQR.excShifts`.
Scaled by $\tilde R$ and centred at $r$ it covers $\mathbb{D}(r, 1.3\tilde R)$ at radius
$0.975\,\varepsilon\tilde R$, its points are $0.965\,\varepsilon\tilde R$ apart, and it has at most
$9/\varepsilon^2$ points. -/
noncomputable def excNet (ε : ℝ) : List ℂ := squareGrid 0 1.3 (3 * ε / 4)

/-- The bad windows of the translate, off the unit square or bringing a point of a separated set
within $\rho\sqrt{\varphi/(11n)}$ of some $\lambda_i$, form a measurable set of probability at
most $\varphi$. -/
private theorem excBad_measurableSet_and_le (S : Finset ℂ) {N : ℕ} (e : Fin N → ℂ) {ρ φ : ℝ}
    (hρ : 0 < ρ) (hφ : 0 ≤ φ) (hφ1 : φ ≤ 1 / 5)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 0.99 * (1 * ρ) ≤ ‖a - b‖) :
    MeasurableSet {x : Fin 2 → ℝ | (∃ j, x j ∉ Set.Icc (0 : ℝ) 1) ∨
        ∃ p ∈ S, ∃ i, ‖p + polarDisk 0 (1 * ρ) x - e i‖ < 1 * ρ * √(φ / (11 * N))} ∧
      (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Icc 0 1)).real
        {x : Fin 2 → ℝ | (∃ j, x j ∉ Set.Icc (0 : ℝ) 1) ∨
          ∃ p ∈ S, ∃ i, ‖p + polarDisk 0 (1 * ρ) x - e i‖ < 1 * ρ * √(φ / (11 * N))} ≤ φ := by
  set A : Set (Fin 2 → ℝ) := ⋃ j, (fun x : Fin 2 → ℝ => x j) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ
  set B : Set (Fin 2 → ℝ) :=
    {x | ∃ p ∈ S, ∃ i, ‖p + polarDisk 0 (1 * ρ) x - e i‖ < 1 * ρ * √(φ / (11 * N))}
  have hAB : {x : Fin 2 → ℝ | (∃ j, x j ∉ Set.Icc (0 : ℝ) 1) ∨
      ∃ p ∈ S, ∃ i, ‖p + polarDisk 0 (1 * ρ) x - e i‖ < 1 * ρ * √(φ / (11 * N))} = A ∪ B := by
    ext x; simp [A, B]
  have hmeas : Measurable (polarDisk 0 (1 * ρ)) := by unfold polarDisk; fun_prop
  have hA : MeasurableSet A :=
    MeasurableSet.iUnion fun j => (measurableSet_Icc.compl).preimage (measurable_pi_apply j)
  have hB : MeasurableSet B := by
    have : B = ⋃ p ∈ S, ⋃ i, {x | ‖p + polarDisk 0 (1 * ρ) x - e i‖ <
        1 * ρ * √(φ / (11 * N))} := by ext; simp [B]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun p _ => MeasurableSet.iUnion fun i =>
      measurableSet_lt (by fun_prop) measurable_const
  rw [hAB]
  refine ⟨hA.union hB, ?_⟩
  set μ := Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Icc 0 1)
  have hA0 : μ A = 0 := by
    refine measure_iUnion_null fun j => Measure.pi_eval_preimage_null _ ?_
    rw [Measure.restrict_apply' measurableSet_Icc, Set.compl_inter_self, measure_empty]
  have : IsFiniteMeasure μ := by infer_instance
  calc μ.real (A ∪ B) ≤ μ.real A + μ.real B := measureReal_union_le _ _
    _ = μ.real B := by rw [measureReal_def, hA0, ENNReal.toReal_zero, zero_add]
    _ ≤ φ := excTranslate_bad_window_le S e (by positivity) hφ hφ1 hS

section Program

variable {O Q : Type} [Has ScalarOp O] [Has DiskSampleOp O]

/-- **The rounded exceptional shifts** (`Exc` in floating point, corrected
[BanksGarzaVargasSrivastava2022, Lemma 5.3]): on a scalar machine with the standard model at
$\boldsymbol{u} \le 1/100$ and an exact polar sampler on a stream `s` uniform on $[0, 1]$, let
the centre $r$ be stored at `C`, the radius $\tilde R > 0$ at `Rt`, the factor $\varepsilon/2$
at `Cw`, $0 < \varepsilon \le 1/2$, and the net `NLAlib.ShiftedQR.excNet ε` at `G`; let
$\lambda_1, \dots, \lambda_n$ be complex numbers, $0 \le \varphi \le 1/5$,
$q = \varphi/(11n)$, and the rounding budget $6\boldsymbol{u}(\lvert r\rvert + 3\tilde R)$ at
most $0.005\,\varepsilon\tilde R$ and at most $\varepsilon\tilde R\sqrt q/8$. Then
`NLAlib.ShiftedQR.excShifts` writes only its output and, except with probability at most
$\varphi$ over its two draws, stores a list $\mathcal{S}$ of shifts with
$\lvert\mathcal{S}\rvert \le 9/\varepsilon^2$ that covers $\mathbb{D}(r, \tilde R)$ at radius
$\varepsilon\tilde R$, keeps the distance $\varepsilon\tilde R\sqrt q/4$ from every
$\lambda_i$, and lies in $\mathbb{D}(r, 2.1\tilde R)$: the hypotheses `hcover`, `hcard` and
`hne` of `NLAlib.exists_mem_le_norm_inv_pow_of_covers` at the radius $\tilde R$, and a
forward-stability distance for the shifted steps. The translate has radius
$\mathrm{fl}(\varepsilon\tilde R/2)$, and its points are not intersected with a disk (the
paper's intersection can drop the points covering the boundary, errata G13ii); the rounding
budget $0.005\,\varepsilon\tilde R$ replaces the paper's $0.1\,\varepsilon\tilde R$, which
exceeds the covering slack (errata G13i), and the packing count is $11$, not $3$ (G13iii). -/
theorem excShifts_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) {law : ℕ → Measure ℝ} {s : ℕ} (hD : IsPolarDiskSampler s I)
    (hU : law s = volume.restrict (Set.Icc 0 1)) {N : ℕ} (e : Fin N → ℂ) {r : ℂ} {R ε φ : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hφ : 0 ≤ φ) (hφ1 : φ ≤ 1 / 5)
    (hu : u ≤ 1 / 100) (hδ : 6 * u * (‖r‖ + 3 * R) ≤ 0.005 * ε * R)
    (hδη : 6 * u * (‖r‖ + 3 * R) ≤ ε * R * √(φ / (11 * N)) / 8) {c rt cw g ss : ℕ × ℕ} :
    PWrites law I (excShifts (O := O) (Q := Q)).body
      (Env.frame [(excNet ε).length] [c, rt, cw, g, ss])
      (Store.inBlock ss.1 ss.2 (2 * (excNet ε).length))
      (fun μ => μ.Live [c, rt, cw, g, ss] ∧ μ.store.get c.1 c.2 = some r.re ∧
        μ.store.get c.1 (c.2 + 1) = some r.im ∧ μ.store.get rt.1 rt.2 = some R ∧
        μ.store.get cw.1 cw.2 = some (ε / 2) ∧
        μ.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧
        ss.2 + 2 * (excNet ε).length ≤ μ.store.len ss.1 ∧
        Fp.Disj (Store.inBlock ss.1 ss.2 (2 * (excNet ε).length)) (Store.inBlock rt.1 rt.2 1) ∧
        Fp.Disj (Store.inBlock ss.1 ss.2 (2 * (excNet ε).length))
          (Store.inBlock g.1 g.2 (2 * (excNet ε).length)))
      (fun μ' => ∃ zs : List ℂ, zs.length = (excNet ε).length ∧
        μ'.store.readBlock ss.1 ss.2 (2 * (excNet ε).length) =
          some (zs.flatMap fun z => [z.re, z.im]) ∧
        (zs.length : ℝ) ≤ 9 / ε ^ 2 ∧ (∀ z : ℂ, ‖z - r‖ ≤ R → ∃ s ∈ zs, ‖z - s‖ ≤ ε * R) ∧
        (∀ s ∈ zs, ∀ i, ε * R * √(φ / (11 * N)) / 4 ≤ ‖e i - s‖) ∧
        ∀ s ∈ zs, ‖s - r‖ ≤ 2.1 * R) φ := by
  classical
  have hu0 := hM.roundoff_nonneg
  set ρw := M.mul (ε / 2) R with hρw
  have hρ := hM.mul (ε / 2) R
  simp only [id] at hρ
  rw [abs_of_pos (by positivity : 0 < ε / 2 * R)] at hρ
  have hρlo : (1 - u) * (ε / 2 * R) ≤ ρw := by linarith [(abs_le.mp hρ).1]
  have hρhi : ρw ≤ (1 + u) * (ε / 2 * R) := by linarith [(abs_le.mp hρ).2]
  have hρ0 : 0 < ρw := lt_of_lt_of_le (by nlinarith) hρlo
  set S := (squareGrid r (R * 1.3) (3 * ε / 4)).toFinset
  set Bad : Set (Fin 2 → ℝ) := {x | (∃ j, x j ∉ Set.Icc (0 : ℝ) 1) ∨
    ∃ p ∈ S, ∃ i, ‖p + polarDisk 0 (1 * ρw) x - e i‖ < 1 * ρw * √(φ / (11 * N))} with hBad
  have hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 0.99 * (1 * ρw) ≤ ‖a - b‖ := by
    intro a ha b hb hab
    have h := squareGrid_pairwise_separated r (by positivity : (0 : ℝ) ≤ R * 1.3)
      (by positivity : (0 : ℝ) < 3 * ε / 4) (by linarith) a (List.mem_toFinset.mp ha) b
      (List.mem_toFinset.mp hb) hab
    have : ρw ≤ 3 * ε / 4 * (R * 1.3) := by nlinarith
    linarith
  obtain ⟨hBm, hBφ⟩ := excBad_measurableSet_and_le S e hρ0 hφ hφ1 hsep
  refine PWrites.of_window (s := s) (W := 2) (Bad := fun _ => Bad)
    (measurable_snd hBm) (fun _ _ => by rw [hU]; exact hBφ) ?_
  rintro μ τ ⟨hl, hcr, hci, hrt, hcw, hg, hss, hsr, hsg⟩ hgood
  refine (excShifts_writes_word (τ := τ) hS hD hcr hci hrt hcw hg hss hl hsr hsg).mono le_rfl ?_
  rintro μ' - ⟨-, hblk⟩
  set W := excSample τ s μ.pos ρw
  simp only [hBad, Set.mem_ofPred_eq, not_or, not_exists, one_mul] at hgood
  obtain ⟨hsq, hfar⟩ := hgood
  have hW : ‖W‖ ≤ ρw := norm_polarDisk_le hρ0.le fun j => not_not.mp (hsq j)
  obtain ⟨hcard, hcov, hdist, hnear⟩ := excShifts_props hM e hR hε hε2 hu hρlo hρhi hW
    (fun p hp i => not_lt.mp fun h => hfar p ⟨List.mem_toFinset.mpr hp, i, h⟩) hδ hδη
  exact ⟨_, List.length_map _, by simpa [excNet] using hblk, hcard, hcov, hdist, hnear⟩

end Program

end NLAlib.ShiftedQR
