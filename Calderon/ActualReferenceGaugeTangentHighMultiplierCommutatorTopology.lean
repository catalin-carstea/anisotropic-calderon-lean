import Calderon.ActualReferenceGaugeTangentHighMultiplierCommutator
import Calderon.NativeOrderOneCoefficientMultiplierTopology

/-! Exact compact actual coefficient topology. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeOrderOneCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

lemma contDiff_referenceGaugeTangentSecondHighMultiplierCommutatorFamily
    (Q : SmoothCoefficientJets 3) :
    ContDiff ℝ ∞ (referenceGaugeTangentSecondHighMultiplierCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q) := by
  have hCoeff (i j : Fin 3) : ContDiff ℝ ∞
      (fun p => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 3 i j p)) := by
    unfold referenceGaugeTangentSecondRotationJetsFamily
    exact contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (referenceGaugeTangentSecondRotationCoefficient g L Φ a i j)
      (contDiff_referenceGaugeTangentSecondRotationCoefficient g L y0 Φ B ε C ρ H a w hData hg i j)
      (Metric.closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (referenceGaugeTangentSecondRotationCoefficient_support g L y0 Φ B ε C ρ H a w hData i j)
  unfold referenceGaugeTangentSecondHighMultiplierCommutatorFamily
    nativeThreeHalfRotationFieldCommutatorGainL
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact (hCoeff i j).clm_comp contDiff_const

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentSecondHighMultiplierCommutatorFamily
