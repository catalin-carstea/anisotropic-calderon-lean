import Calderon.RadiusTwoBoundedCoefficientCutoffEnergy
import Calderon.RadiusTwoNativeSourceFoundation

/-! EXPANSION.json precedes the exact original metric specialization. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local irreducible] TauCeti.W1p.contDiffSMulL TauCeti.PDE.energyFormH1

run_cmd Lean.logInfo "BEFORE HEADER original metric cutoff energy"

theorem radiusTwoMetricEnergy_smoothCutoff_difference
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |χ x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient χ x‖ ≤ M)
    (u v : RadiusTwoH1) :
    let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL χ hχ hM hAbs hGrad
    TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ) (S u) v -
      TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ) u (S v) =
        ∫ x in radiusTwoOpens,
          TauCeti.W1p.value u x * TauCeti.PDE.matrixBilinearForm (principalCoefficient g x)
            (TauCeti.W1p.gradient v x) (gradient χ x) -
          TauCeti.W1p.value v x * TauCeti.PDE.matrixBilinearForm (principalCoefficient g x)
            (gradient χ x) (TauCeti.W1p.gradient u x) ∂(volume : Measure R3) := by
  trace "PROOFENTER original metric cutoff energy"
  exact radiusTwoBoundedCoefficientEnergy_smoothCutoff_difference (principalCoefficient g)
    (memLp_radiusTwoMetricEnergyIntegrand g hg) χ hχ hM hAbs hGrad u v

end OAI.AnisotropicCalderon.ExteriorSource
