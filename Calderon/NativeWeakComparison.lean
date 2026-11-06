import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.Sobolev.W1p.ChainRule

/-! EXPANSION.json precedes these transparent exact pinned weak-comparison proof leaves. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set TopologicalSpace
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open TauCeti TauCeti.PDE
variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

@[simp]
theorem energyFormH1_posPart_right (u : W1p mu Omega 2) :
    energyFormH1 a b c u (W1p.posPart (by norm_num) u) =
      energyFormH1 a b c (W1p.posPart (by norm_num) u) (W1p.posPart (by norm_num) u) := by
  classical
  simp only [energyFormH1_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_posPart (W1p.value u),
    W1p.gradient_posPart_ae (by norm_num) u] with x hv hg
  have hvalue : W1p.value (W1p.posPart (by norm_num) u) x = max (W1p.value u x) 0 := by
    rw [W1p.value_posPart]
    exact hv
  -- The indicator set is passed explicitly: `hx` is stated as an inequality, and the
  -- indicator lemmas cannot infer the set `{y | 0 < W1p.value u y}` from it alone.
  by_cases hx : 0 < W1p.value u x
  · have hjet : jetField (W1p.posPart (by norm_num) u) x = jetField u x := by
      rw [jetField_apply, hvalue, hg, max_eq_left hx.le,
        indicator_of_mem (s := {y | 0 < W1p.value u y}) hx, jetField_apply]
    rw [hjet]
  · have hjet : jetField (W1p.posPart (by norm_num) u) x = 0 := by
      rw [jetField_apply, hvalue, hg, max_eq_right (le_of_not_gt hx),
        indicator_of_notMem (s := {y | 0 < W1p.value u y}) hx]
      rfl
    rw [hjet]
    simp only [map_zero]

theorem value_eq_zero_of_energyFormH1_self_nonpos {C : ℝ} (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    {w : W1p0 mu Omega 2}
    (hw : energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2) ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value (w : W1p mu Omega 2) x = 0 := by
  have hnorm : ‖w‖ = 0 := by
    have hbound := (hlower w).trans hw
    apply le_antisymm ?_ (norm_nonneg w)
    exact le_of_not_gt fun hpos ↦ (not_lt_of_ge hbound) (mul_pos hC (pow_pos hpos 2))
  have hw : (w : W1p mu Omega 2) = 0 :=
    congrArg (fun v : W1p0 mu Omega 2 ↦ (v : W1p mu Omega 2)) (norm_eq_zero.mp hnorm)
  have hzero : W1p.value (w : W1p mu Omega 2) = 0 := by
    rw [hw, ← W1p.valueL_apply, map_zero]
  rw [hzero]
  exact Lp.coeFn_zero (E := ℝ) (p := 2) (μ := mu.restrict Omega)

theorem value_nonpos_of_energyFormH1_nonpos {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    {C : ℝ} (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ 0 := by
  let w : W1p0 mu Omega 2 := ⟨W1p.posPart (by norm_num) u, hboundary⟩
  have hvalue : ∀ᵐ x ∂mu.restrict Omega,
      W1p.value (w : W1p mu Omega 2) x = max (W1p.value u x) 0 := by
    dsimp only [w]
    rw [W1p.value_posPart]
    exact Lp.coeFn_posPart (W1p.value u)
  have hnonneg : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x :=
    hvalue.mono fun x hx ↦ hx.symm ▸ le_max_right _ _
  have henergy := hu w hnonneg
  dsimp only [w] at henergy
  rw [energyFormH1_posPart_right] at henergy
  filter_upwards [hvalue, value_eq_zero_of_energyFormH1_self_nonpos (w := w) hC hlower henergy]
    with x hx hz
  rw [hz] at hx
  exact (le_max_left _ _).trans hx.symm.le

theorem value_le_of_energyFormH1_le {u v : W1p mu Omega 2}
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hboundary : W1p.posPart (by norm_num) (u - v) ∈ w1p0Submodule mu Omega 2)
    {C : ℝ} (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (huv : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        energyFormH1 a b c u (w : W1p mu Omega 2) ≤
          energyFormH1 a b c v (w : W1p mu Omega 2)) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  classical
  have hsub := value_nonpos_of_energyFormH1_nonpos hboundary hC hlower (by
    intro w hw
    rw [← energyFormH1L_apply hcoeff]
    simpa only [map_sub, sub_apply, energyFormH1L_apply] using
      sub_nonpos.mpr (huv w hw))
  have hvalue : W1p.value (u - v) = W1p.value u - W1p.value v := by
    simp only [← W1p.valueL_apply, map_sub]
  filter_upwards [hsub, Lp.coeFn_sub (W1p.value u) (W1p.value v)] with x hx hval
  rw [hvalue, hval, Pi.sub_apply] at hx
  exact sub_nonpos.mp hx

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.energyFormH1_posPart_right
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.value_eq_zero_of_energyFormH1_self_nonpos
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.value_nonpos_of_energyFormH1_nonpos
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.value_le_of_energyFormH1_le
