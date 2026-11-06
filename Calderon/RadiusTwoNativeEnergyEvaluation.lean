import Calderon.RadiusTwoNativeEnergyConstructor

/-! EXPANSION.json precedes exact physical evaluation/raw correspondence/coercivity transport. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma radiusTwoMetricEnergyL0Normalized_apply (g : MatrixField) (hg : IsAdmissibleMetric g)
    (u v : RadiusTwoH1Zero) :
    radiusTwoMetricEnergyL0Normalized g hg u v =
      TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0
        (u : RadiusTwoH1) (v : RadiusTwoH1) := by
  unfold radiusTwoMetricEnergyL0Normalized
  exact TauCeti.PDE.energyFormH1L0_apply (memLp_radiusTwoMetricEnergyIntegrand g hg) u v

lemma radiusTwoMetricEnergyL0Normalized_apply_eq_raw (g : MatrixField) (hg : IsAdmissibleMetric g)
    (u v : RadiusTwoH1Zero) :
    radiusTwoMetricEnergyL0Normalized g hg u v =
      TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := radiusTwoOpens)
        (a := principalCoefficient g) (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ))
        (memLp_radiusTwoMetricEnergyIntegrand g hg) u v := by
  exact (radiusTwoMetricEnergyL0Normalized_apply g hg u v).trans
    (TauCeti.PDE.energyFormH1L0_apply (memLp_radiusTwoMetricEnergyIntegrand g hg) u v).symm

lemma isCoercive_radiusTwoMetricEnergyL0Normalized (g : MatrixField) (hg : IsAdmissibleMetric g) :
    IsCoercive (radiusTwoMetricEnergyL0Normalized g hg) := by
  rcases isCoercive_radiusTwoMetricEnergy g hg with ⟨C,hC,hBound⟩
  refine ⟨C,hC,?_⟩
  intro v
  calc
    C * ‖v‖ * ‖v‖ ≤ TauCeti.PDE.energyFormH1L0
        (mu := (volume : Measure R3)) (Omega := radiusTwoOpens)
        (a := principalCoefficient g) (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ))
        (memLp_radiusTwoMetricEnergyIntegrand g hg) v v := hBound v
    _ = radiusTwoMetricEnergyL0Normalized g hg v v :=
      (radiusTwoMetricEnergyL0Normalized_apply_eq_raw g hg v v).symm

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricEnergyL0Normalized_apply
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricEnergyL0Normalized_apply_eq_raw
#print axioms OAI.AnisotropicCalderon.ExteriorSource.isCoercive_radiusTwoMetricEnergyL0Normalized
