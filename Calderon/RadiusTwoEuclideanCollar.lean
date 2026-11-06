import Calderon.RadiusTwoNativeSourceFoundation
import Calderon.NativePrincipalEnergyGradientForm
import Calderon.MetricSmooth

/-! EXPANSION.json precedes exact actual exterior Euclidean collar identities. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open EnergyBridge

def radiusTwoCollarOpens (a : ℝ) : Opens R3 :=
  ⟨{x : R3 | a < ‖x‖ ∧ ‖x‖ < 2},
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)⟩

lemma mem_radiusTwoCollarOpens (a : ℝ) (x : R3) :
    x ∈ radiusTwoCollarOpens a ↔ a < ‖x‖ ∧ ‖x‖ < 2 := Iff.rfl

lemma radiusTwoCollarOpens_le_radiusTwoOpens (a : ℝ) :
    radiusTwoCollarOpens a ≤ radiusTwoOpens := by
  intro x hx
  change x ∈ ball (0 : R3) 2
  exact mem_ball_zero_iff.mpr hx.2

lemma principalCoefficient_eq_one_on_radiusTwoCollar
    (g : MatrixField) (hg : IsAdmissibleMetric g) (a : ℝ) (ha : 1 ≤ a)
    (x : R3) (hx : x ∈ radiusTwoCollarOpens a) : principalCoefficient g x = 1 := by
  exact principalCoefficient_eq_one_of_exterior g hg x (ha.trans hx.1.le)

lemma nativeMetricEnergy_eq_identity_on_radiusTwoCollar
    (g : MatrixField) (hg : IsAdmissibleMetric g) (a : ℝ) (ha : 1 ≤ a)
    (u v : TauCeti.W1p (volume : Measure R3) (radiusTwoCollarOpens a) 2) :
    TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ) u v =
      TauCeti.PDE.energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (0 : R3 → R3) (0 : R3 → ℝ) u v := by
  rw [nativePrincipalEnergy_eq_gradient_setIntegral,nativePrincipalEnergy_eq_gradient_setIntegral]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (radiusTwoCollarOpens a).isOpen.measurableSet] with x hx
  rw [principalCoefficient_eq_one_on_radiusTwoCollar g hg a ha x hx]

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoCollarOpens
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.mem_radiusTwoCollarOpens
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoCollarOpens_le_radiusTwoOpens
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.principalCoefficient_eq_one_on_radiusTwoCollar
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.nativeMetricEnergy_eq_identity_on_radiusTwoCollar
