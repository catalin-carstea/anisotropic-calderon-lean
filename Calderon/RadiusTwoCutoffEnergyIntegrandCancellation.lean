import Calderon.RadiusTwoSmoothCutoffJet
import Calderon.NativeCoordinateEnergyCancellation
import Calderon.PrincipalZeroDriftIntegrand

/-! EXPANSION.json precedes the focused actual arbitrary-coefficient energy cancellation. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily.DriftBootstrap
attribute [local irreducible] TauCeti.W1p.contDiffSMulL

run_cmd Lean.logInfo "BEFORE HEADER actual cutoff integrand cancellation"

theorem radiusTwoBoundedCoefficient_cutoff_integrand_difference_ae
    (A : MatrixField)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |χ x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient χ x‖ ≤ M)
    (u v : RadiusTwoH1) :
    let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL χ hχ hM hAbs hGrad
    ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
      TauCeti.PDE.energyIntegrand (A x) (0 : R3) (0 : ℝ)
          (TauCeti.PDE.jetField (S u) x) (TauCeti.PDE.jetField v x) -
        TauCeti.PDE.energyIntegrand (A x) (0 : R3) (0 : ℝ)
          (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField (S v) x) =
        TauCeti.W1p.value u x * TauCeti.PDE.matrixBilinearForm (A x)
          (TauCeti.W1p.gradient v x) (gradient χ x) -
        TauCeti.W1p.value v x * TauCeti.PDE.matrixBilinearForm (A x)
          (gradient χ x) (TauCeti.W1p.gradient u x) := by
  trace "PROOFENTER actual cutoff integrand cancellation"
  filter_upwards [radiusTwoSmoothCutoff_jetField_ae χ hχ hM hAbs hGrad u,
    radiusTwoSmoothCutoff_jetField_ae χ hχ hM hAbs hGrad v] with x hu hv
  rw [hu,hv]
  have hCancel := realBilinear_coordinate_product_cancel
    (TauCeti.PDE.energyIntegrand (A x) (0 : R3) (0 : ℝ))
    (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x)
    ((0 : ℝ),gradient χ x) (χ x) (TauCeti.W1p.value u x) (TauCeti.W1p.value v x)
  simpa only [Pi.zero_apply,principalZeroDrift_energyIntegrand,TauCeti.PDE.jetField_apply] using hCancel


end OAI.AnisotropicCalderon.ExteriorSource
