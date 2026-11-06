import Calderon.ActualReferenceRotationWeakConormalTopology
import Calderon.ActualReferenceAdjointConormalGreenPairing
import Calderon.ActualReferenceAngleConormalCovariance
import Calderon.ActualReferenceRotationAdjointLowerEnergy
import Calderon.NativeSupportedAdjointConormalPairing
import Calderon.ActualReferenceRotationAdjointLowConormalFamily
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace


variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceRotationLiteralSupportedOriginalZeroEnergyL_isInvertible (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible) :
    (nativeSupportedOriginalZeroEnergyL (fun x => coordinateRotationPrincipalFamily i j a (t,x))
      (referenceRotationPrincipalEnergyIntegrand_memLp g L y0 Φ B ε C ρ H a w hData i j t)
      (0 : SmoothCoefficientJets 1)
      (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      (SpatialJetFields.contDiff_spatial_slice _
        (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1 t)).IsInvertible := by
  have hA := referenceRotationWeakDirichletEnergyFamily_eq_nativeEnergyFormH1L0
    g L y0 Φ B ε C ρ H a w hData hcalc i j t
    
  have hC := nativeZeroCoefficientEnergyL_congr_coefficients_for_angle
    (fun x => coordinateRotationPrincipalFamily i j a (t,x)) (fun x => coordinateRotationPrincipalFamily i j a (t,x))
    (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
    (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
    0 (coefficientValue 1 (0 : SmoothCoefficientJets 1))
    (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t)
    (nativeSupportedOriginalEnergyMemLp (fun x => coordinateRotationPrincipalFamily i j a (t,x))
      (referenceRotationPrincipalEnergyIntegrand_memLp g L y0 Φ B ε C ρ H a w hData i j t)
      (0 : SmoothCoefficientJets 1)
      (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      (SpatialJetFields.contDiff_spatial_slice _
        (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1 t)) rfl rfl coefficientValue_zero_one.symm
  have hi := referenceRotationWeakDirichletEnergyFamily_isInvertible_of_original
    g L y0 Φ B ε C ρ H a w hData hcalc i j t.1 t.2 hOriginal
  exact Eq.mp (congrArg
    (fun T : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => T.IsInvertible) (hA.trans hC)) hi

attribute [local irreducible] referenceRotationWeakConormalEndpointFamily
  referenceRotationAdjointWeakConormalEndpointFamily nativeWeakConormalEndpoint

lemma sphereSobolevDualPairing_referenceRotationOriginal_eq_adjoint_add_normal
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible)
    (f z : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) z
      (referenceRotationWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f) =
    sphereSobolevDualPairing (1/2:ℝ) f
      (referenceRotationAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF i j t z) +
    ⟪sphereContinuousScalarMulL (nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData
        (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        (SpatialJetFields.contDiff_spatial_slice _
          (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1 t)))
      (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF z)),
      τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF f)⟫_ℝ := by
  let beta : R3 → R3 := fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)
  have hbeta : ContDiff ℝ ∞ beta :=
    SpatialJetFields.contDiff_spatial_slice _
      (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1 t
  let hp := referenceRotationPrincipalEnergyIntegrand_memLp g L y0 Φ B ε C ρ H a w hData i j t
  let ho := nativeSupportedOriginalEnergyMemLp (fun x => coordinateRotationPrincipalFamily i j a (t,x)) hp (0 : SmoothCoefficientJets 1) beta hbeta
  let ha := nativeSupportedAdjointEnergyMemLp (fun x => coordinateRotationPrincipalFamily i j a (t,x)) hp (0 : SmoothCoefficientJets 1) beta hbeta
  have hPair := sphereSobolevDualPairing_nativeSupportedOriginal_eq_adjoint_add_normal
    τ0 (fun x => coordinateRotationPrincipalFamily i j a (t,x)) hp (0 : SmoothCoefficientJets 1) beta hbeta
    (referenceRotationLiteralSupportedOriginalZeroEnergyL_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc i j t hOriginal) hF f z
  have hO := (referenceRotationWeakConormalEndpointFamily_eq_nativeWeakConormalEndpoint
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j t).trans
      (nativeWeakConormalEndpoint_congr_coefficients _ _ beta beta 0
        (coefficientValue 1 (0 : SmoothCoefficientJets 1))
        (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t) ho hF rfl rfl coefficientValue_zero_one.symm)
  have hNeg : (-beta : R3 → R3) = (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) := rfl
  have hMass : (fun x => coefficientValue 1 (0 : SmoothCoefficientJets 1) x-nativeSupportedDriftDivergence beta x) =
      (fun x => -nativeSupportedDriftDivergence beta x) := by
    funext x
    rw [coefficientValue_zero_one]
    exact zero_sub _
  have hAdj := nativeWeakConormalEndpoint_congr_coefficients _ _ (-beta)
    (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
    (fun x => coefficientValue 1 (0 : SmoothCoefficientJets 1) x-nativeSupportedDriftDivergence beta x)
    (fun x => -nativeSupportedDriftDivergence beta x) ha
    (memLp_referenceRotationAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData i j t) hF rfl hNeg hMass
  have hAdjActual : nativeWeakConormalEndpoint (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
      (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      (fun x => -nativeSupportedDriftDivergence beta x)
      (memLp_referenceRotationAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData i j t) hF =
      referenceRotationAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF i j t := by
    unfold referenceRotationAdjointWeakConormalEndpointFamily
    rfl
  have hLeft := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    sphereSobolevDualPairing (1/2:ℝ) z (T f)) hO
  have hRight := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    sphereSobolevDualPairing (1/2:ℝ) f (T z)) (hAdj.trans hAdjActual)
  exact hLeft.trans (hPair.trans (congrArg (fun t : ℝ => t+⟪sphereContinuousScalarMulL
    (nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData beta hbeta))
    (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF z)),
    τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF f)⟫_ℝ) hRight))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationLiteralSupportedOriginalZeroEnergyL_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceRotationOriginal_eq_adjoint_add_normal
