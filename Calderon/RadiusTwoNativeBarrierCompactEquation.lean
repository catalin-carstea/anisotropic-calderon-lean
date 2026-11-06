import Calderon.RadiusTwoNativePolynomialBarrier
import Calderon.RadiusTwoEuclideanCollar
import Calderon.RadiusTwoPolynomialBarrierCompactFlux

/-! EXPANSION.json precedes the actual native polynomial compact-test equation. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Distributions Gradient
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open TauCeti TauCeti.PDE

lemma radiusTwoBarrier_energy_test_on_collar (a M : ℝ)
    (phi : 𝓓(radiusTwoCollarOpens a, ℝ)) :
    energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (0 : R3 → R3) (0 : R3 → ℝ)
      (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) (radiusTwoBarrierH1 M))
      (W1p.ofTestFunctionₗ (volume : Measure R3) (radiusTwoCollarOpens a) 2 phi) =
      ∫ x in radiusTwoCollarOpens a, (6*M)*phi x ∂(volume : Measure R3) := by
  have hMu : (volume : Measure R3).restrict (radiusTwoCollarOpens a) ≤
      (volume : Measure R3).restrict radiusTwoOpens :=
    Measure.restrict_mono_set volume
      (SetLike.coe_subset_coe.mpr (radiusTwoCollarOpens_le_radiusTwoOpens a))
  have hGrad := (radiusTwoBarrierH1_gradient_ae M).filter_mono (ae_mono hMu)
  have hRestr := W1p.gradient_restrictL_ae (radiusTwoCollarOpens_le_radiusTwoOpens a)
    (radiusTwoBarrierH1 M)
  have hTest := gradientTestFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 phi
  have hIntegral : energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (0 : R3 → R3) (0 : R3 → ℝ)
      (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) (radiusTwoBarrierH1 M))
      (W1p.ofTestFunctionₗ (volume : Measure R3) (radiusTwoCollarOpens a) 2 phi) =
      ∫ x in radiusTwoCollarOpens a, ((∇ (phi : R3 → ℝ) x) : R3) ⬝ᵥ ((-2*M) • x)
        ∂(volume : Measure R3) := by
    rw [nativePrincipalEnergy_eq_gradient_setIntegral]
    apply integral_congr_ae
    filter_upwards [hGrad,hRestr,hTest] with x hG hR hT
    rw [hR,hG,W1p.gradient_ofTestFunctionₗ,hT,matrixBilinearForm_one_apply]
    rw [WithLp.ofLp_smul]
  exact hIntegral.trans (integral_gradient_dot_radialBarrier (radiusTwoCollarOpens a) M phi)

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoBarrier_energy_test_on_collar
