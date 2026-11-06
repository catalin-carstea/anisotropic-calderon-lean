import Calderon.RadiusTwoNativeBarrierCompactEquation
import Calderon.NativeFixedFunctionTestEquationExtension

/-! EXPANSION.json precedes derived actual barrier zero-test equations and supersolution sign. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open TauCeti TauCeti.PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

lemma memLp_const_radiusTwoCollar (a C : ℝ) :
    MemLp (fun _ : R3 => C) 2 ((volume : Measure R3).restrict (radiusTwoCollarOpens a)) := by
  have hMu : (volume : Measure R3).restrict (radiusTwoCollarOpens a) ≤
      (volume : Measure R3).restrict radiusTwoOpens :=
    Measure.restrict_mono_set volume
      (SetLike.coe_subset_coe.mpr (radiusTwoCollarOpens_le_radiusTwoOpens a))
  exact MemLp.mono_measure hMu (memLp_two_radiusTwo_of_continuous (fun _ : R3 => C) continuous_const)

lemma radiusTwoBarrier_energy_zero_test_on_collar (a M : ℝ)
    (v : W1p0 (volume : Measure R3) (radiusTwoCollarOpens a) 2) :
    energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (0 : R3 → R3) (0 : R3 → ℝ)
      (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) (radiusTwoBarrierH1 M))
      (v : W1p (volume : Measure R3) (radiusTwoCollarOpens a) 2) =
      ∫ x in radiusTwoCollarOpens a, (6*M)*W1p.value
        (v : W1p (volume : Measure R3) (radiusTwoCollarOpens a) 2) x ∂(volume : Measure R3) := by
  let f : Lp ℝ 2 ((volume : Measure R3).restrict (radiusTwoCollarOpens a)) :=
    (memLp_const_radiusTwoCollar a (6*M)).toLp (fun _ : R3 => 6*M)
  have hF : f =ᵐ[((volume : Measure R3).restrict (radiusTwoCollarOpens a))]
      (fun _ : R3 => 6*M) := MemLp.coeFn_toLp (memLp_const_radiusTwoCollar a (6*M))
  have hUE := uniformlyEllipticOn_const_one_one (n := Fin 3) (radiusTwoCollarOpens a : Set R3)
  have hc : MemLp (fun x : R3 => energyIntegrand (1 : Matrix (Fin 3) (Fin 3) ℝ)
      (0 : R3) (0 : ℝ)) ⊤ ((volume : Measure R3).restrict (radiusTwoCollarOpens a)) :=
    memLp_energyIntegrand_of_bounds (by norm_num : (0 : ℝ) ≤ 1)
      aestronglyMeasurable_const aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x hx eta xi => hUE.upper_bound hx eta xi)
      (beta := 0) (gamma := 0) (fun _ _ => by simp) (fun _ _ => by simp)
  have hCompact : ∀ phi : 𝓓(radiusTwoCollarOpens a, ℝ),
      energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (0 : R3 → R3) (0 : R3 → ℝ)
        (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) (radiusTwoBarrierH1 M))
        (W1p.ofTestFunctionₗ (volume : Measure R3) (radiusTwoCollarOpens a) 2 phi) =
        ∫ x in radiusTwoCollarOpens a, f x * phi x ∂(volume : Measure R3) := by
    intro phi
    refine (radiusTwoBarrier_energy_test_on_collar a M phi).trans (integral_congr_ae ?_)
    filter_upwards [hF] with x hx
    rw [hx]
  have hEq := native_energy_equation_of_forall_testFunction hc f
    (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) (radiusTwoBarrierH1 M)) hCompact v
  refine hEq.trans ((dirichletForcing_apply_eq_setIntegral f v).trans (integral_congr_ae ?_))
  filter_upwards [hF] with x hx
  rw [hx]

lemma radiusTwoBarrier_energy_nonneg_on_collar (a M : ℝ) (hM : 0 ≤ M)
    (v : W1p0 (volume : Measure R3) (radiusTwoCollarOpens a) 2)
    (hv : ∀ᵐ x ∂(volume : Measure R3).restrict (radiusTwoCollarOpens a),
      0 ≤ W1p.value (v : W1p (volume : Measure R3) (radiusTwoCollarOpens a) 2) x) :
    0 ≤ energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (0 : R3 → R3) (0 : R3 → ℝ)
      (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) (radiusTwoBarrierH1 M))
      (v : W1p (volume : Measure R3) (radiusTwoCollarOpens a) 2) := by
  rw [radiusTwoBarrier_energy_zero_test_on_collar]
  apply integral_nonneg_of_ae
  filter_upwards [hv] with x hx
  exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hM) hx

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.memLp_const_radiusTwoCollar
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoBarrier_energy_zero_test_on_collar
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoBarrier_energy_nonneg_on_collar
