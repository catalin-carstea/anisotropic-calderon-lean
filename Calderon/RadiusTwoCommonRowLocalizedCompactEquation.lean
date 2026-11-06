import Calderon.RadiusTwoCutoffSourceEquationOfZeroTest
import Calderon.RadiusTwoCommonRowOffPoleWeakEquation
import Calderon.RadiusTwoNativeCutoffTestProduct

/-! EXPANSION.json precedes actual localized row identification with the EXISTING solver. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Distributions Gradient InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoCommonRow_localized_compactTest_equation
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
    (χ : R3 → ℝ) (w : RadiusTwoH1Zero)
    (hValue : (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z : R3 => χ z * K z))
    (η : 𝓓(radiusTwoOpens, ℝ))
    (hOne : ∀ z ∈ tsupport (η : R3 → ℝ), χ z = 1)
    (hPole : (2 : ℝ) • q ∉ tsupport (η : R3 → ℝ))
    {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |η x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient (η : R3 → ℝ) x‖ ≤ M)
    (φ : 𝓓(radiusTwoOpens, ℝ)) :
    let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 :=
      TauCeti.W1p.contDiffSMulL (η : R3 → ℝ) η.contDiff hM hAbs hGrad
    TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      (S (w : RadiusTwoH1)) (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) =
      ∫ x in radiusTwoOpens,
        radiusTwoFixedRowCutoffForcingLp g hg ⟨η,η.contDiff⟩ (w : RadiusTwoH1) x * φ x
          ∂(volume : Measure R3) := by
  trace "PROOFENTER actual localized compact source equation"
  let ηData : SmoothData := ⟨η,η.contDiff⟩
  let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 :=
    TauCeti.W1p.contDiffSMulL (η : R3 → ℝ) η.contDiff hM hAbs hGrad
  let Φ : 𝓓(radiusTwoOpens, ℝ) := radiusTwoTestProduct η φ
  have hSupp : tsupport (Φ : R3 → ℝ) ⊆ tsupport (η : R3 → ℝ) :=
    tsupport_radiusTwoTestProduct_subset_left η φ
  have hOff :
      TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
        (w : RadiusTwoH1) (nativeZeroTestLinear radiusTwoOpens Φ : RadiusTwoH1) = 0 :=
    radiusTwoCommonRow_cutoff_offpole_weak_equation g hg a ha ha1 q hq K hLimit χ w hValue Φ
      (fun y hy => hOne y (hSupp hy)) (fun h => hPole (hSupp h))
  have hProduct : S (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) =
      (nativeZeroTestLinear radiusTwoOpens Φ : RadiusTwoH1) :=
    nativeZeroTest_radiusTwoTestProduct η φ hM hAbs hGrad
  have hZero :
      TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
        (w : RadiusTwoH1) (S (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1)) = 0 :=
    (congrArg (fun v : RadiusTwoH1 => TauCeti.PDE.energyFormH1 (principalCoefficient g)
      (0 : R3 → R3) (0 : R3 → ℝ) (w : RadiusTwoH1) v) hProduct).trans hOff
  exact radiusTwoMetric_cutoff_sourceEquation_of_zero_test g hg ηData hM hAbs hGrad
    (w : RadiusTwoH1) φ hZero

end OAI.AnisotropicCalderon.ExteriorSource
