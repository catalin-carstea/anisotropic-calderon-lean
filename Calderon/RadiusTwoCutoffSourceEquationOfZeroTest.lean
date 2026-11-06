import Calderon.RadiusTwoFixedRowCutoffCommutator
import Calderon.RadiusTwoFixedRowForcingTestIntegral

/-! EXPANSION.json precedes actual native cutoff algebra outside any common-row limit context. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal Distributions Gradient
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

theorem radiusTwoMetric_cutoff_sourceEquation_of_zero_test
    (g : MatrixField) (hg : IsAdmissibleMetric g) (η : SmoothData)
    {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |η.1 x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient η.1 x‖ ≤ M)
    (u : RadiusTwoH1) (φ : 𝓓(radiusTwoOpens, ℝ))
    (hZero : TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      u ((TauCeti.W1p.contDiffSMulL η.1 η.2 hM hAbs hGrad)
        (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1)) = 0) :
    let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL η.1 η.2 hM hAbs hGrad
    TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      (S u) (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) =
      ∫ x in radiusTwoOpens, radiusTwoFixedRowCutoffForcingLp g hg η u x * φ x
        ∂(volume : Measure R3) := by
  trace "PROOFENTER native cutoff zero-test algebra"
  let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL η.1 η.2 hM hAbs hGrad
  have hComm := radiusTwoMetricEnergy_cutoff_commutator_eq_forcing g hg η hM hAbs hGrad u φ
  change TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      (S u) (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) -
    TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      u (S (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1)) =
      ∫ x in radiusTwoOpens, radiusTwoFixedRowCutoffForcing g hg η u x * φ x
        ∂(volume : Measure R3) at hComm
  rw [hZero,sub_zero] at hComm
  trace "COMMUTATOR ZERO native cutoff zero-test algebra"
  have hIntegral := integral_radiusTwoFixedRowCutoffForcingLp_mul_test g hg η u φ
  exact hComm.trans hIntegral.symm

end OAI.AnisotropicCalderon.ExteriorSource
