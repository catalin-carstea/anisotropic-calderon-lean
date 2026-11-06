import Calderon.RadiusTwoNativeSourceFoundation
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

theorem radiusTwoMetricEnergy_coefficient_isSymm_ae
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
      (principalCoefficient g x).IsSymm :=
  Filter.Eventually.of_forall (fun x => (principalCoefficient_posDef g hg x).isHermitian.isSymm)

theorem radiusTwoMetricEnergy_symm
    (g : MatrixField) (hg : IsAdmissibleMetric g) (u v : RadiusTwoH1) :
    TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ) u v =
      TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ) v u := by
  have h := TauCeti.PDE.energyFormH1_comm_of_isSymm_ae
    (mu := (volume : Measure R3)) (Omega := radiusTwoOpens)
    (a := principalCoefficient g) (c := (0 : R3 → ℝ))
    (radiusTwoMetricEnergy_coefficient_isSymm_ae g hg) u v
  simpa only [Pi.zero_def] using h

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricEnergy_coefficient_isSymm_ae
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricEnergy_symm
