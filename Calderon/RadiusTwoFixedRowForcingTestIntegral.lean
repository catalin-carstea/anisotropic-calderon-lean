import Calderon.RadiusTwoFixedRowCutoffForcing

/-! Full EXPANSION.json precedes unconditional actual forcing/test integral transport. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

theorem integral_radiusTwoFixedRowCutoffForcingLp_mul_test
    (g : MatrixField) (hg : IsAdmissibleMetric g) (η : SmoothData)
    (u : RadiusTwoH1) (φ : 𝓓(radiusTwoOpens, ℝ)) :
    (∫ x in radiusTwoOpens, radiusTwoFixedRowCutoffForcingLp g hg η u x * φ x
      ∂(volume : Measure R3)) =
    ∫ x in radiusTwoOpens, radiusTwoFixedRowCutoffForcing g hg η u x * φ x
      ∂(volume : Measure R3) := by
  apply integral_congr_ae
  filter_upwards [radiusTwoFixedRowCutoffForcingLp_apply_ae g hg η u] with x hx
  exact congrArg (fun t : ℝ => t * φ x) hx

end OAI.AnisotropicCalderon.ExteriorSource
