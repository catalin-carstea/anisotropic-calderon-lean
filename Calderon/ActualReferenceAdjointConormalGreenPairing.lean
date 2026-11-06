import Calderon.ActualReferenceNativeConormalEndpoint
import Calderon.ActualReferenceAngleConormalCovariance
import Calderon.ActualReferenceAdjointLowerEnergy
import Calderon.NativeSupportedAdjointConormalPairing
import Calderon.ActualReferenceAdjointLowConormalFamily
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma coefficientValue_zero_one : coefficientValue 1 (0 : SmoothCoefficientJets 1) = (0 : R3 → ℝ) := rfl

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceSupportedOriginalZeroEnergyL_isInvertible (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (nativeSupportedOriginalZeroEnergyL (fun x => a (p,x))
      (referencePrincipalEnergyIntegrand_memLp g L y0 Φ B ε C ρ H a w hData p)
      (0 : SmoothCoefficientJets 1)
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
      ((jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1.comp
        (contDiff_const.prodMk contDiff_id))).IsInvertible := by
  have hA := referenceWeakDirichletEnergyFamily_eq_nativeEnergyFormH1L0
    g L y0 Φ B ε C ρ H a w hData hcalc p
    (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p)
  have hC := nativeZeroCoefficientEnergyL_congr_coefficients_for_angle
    (fun x => a (p,x)) (fun x => a (p,x))
    (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
    (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
    0 (coefficientValue 1 (0 : SmoothCoefficientJets 1))
    (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p)
    (nativeSupportedOriginalEnergyMemLp (fun x => a (p,x))
      (referencePrincipalEnergyIntegrand_memLp g L y0 Φ B ε C ρ H a w hData p)
      (0 : SmoothCoefficientJets 1)
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
      ((jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1.comp
        (contDiff_const.prodMk contDiff_id))) rfl rfl coefficientValue_zero_one.symm
  exact Eq.mp (congrArg
    (fun T : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => T.IsInvertible) (hA.trans hC)) hOriginal

attribute [local irreducible] referenceWeakConormalEndpointFamily
  referenceAdjointWeakConormalEndpointFamily nativeWeakConormalEndpoint

lemma sphereSobolevDualPairing_referenceOriginal_eq_adjoint_add_normal
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f z : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) z
      (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) =
    sphereSobolevDualPairing (1/2:ℝ) f
      (referenceAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF p z) +
    ⟪sphereContinuousScalarMulL (nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData
        (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
        ((jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1.comp
          (contDiff_const.prodMk contDiff_id))))
      (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF z)),
      τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF f)⟫_ℝ := by
  let beta : R3 → R3 := fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)
  have hbeta : ContDiff ℝ ∞ beta :=
    (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1.comp
      (contDiff_const.prodMk contDiff_id)
  let hp := referencePrincipalEnergyIntegrand_memLp g L y0 Φ B ε C ρ H a w hData p
  let ho := nativeSupportedOriginalEnergyMemLp (fun x => a (p,x)) hp (0 : SmoothCoefficientJets 1) beta hbeta
  let ha := nativeSupportedAdjointEnergyMemLp (fun x => a (p,x)) hp (0 : SmoothCoefficientJets 1) beta hbeta
  have hPair := sphereSobolevDualPairing_nativeSupportedOriginal_eq_adjoint_add_normal
    τ0 (fun x => a (p,x)) hp (0 : SmoothCoefficientJets 1) beta hbeta
    (referenceSupportedOriginalZeroEnergyL_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc p hOriginal) hF f z
  have hO := (referenceWeakConormalEndpointFamily_eq_nativeWeakConormalEndpoint
    g L y0 Φ B ε C ρ H a w hData hcalc hF p).trans
      (nativeWeakConormalEndpoint_congr_coefficients _ _ beta beta 0
        (coefficientValue 1 (0 : SmoothCoefficientJets 1))
        (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p) ho hF rfl rfl coefficientValue_zero_one.symm)
  have hNeg : (-beta : R3 → R3) = (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) := rfl
  have hMass : (fun x => coefficientValue 1 (0 : SmoothCoefficientJets 1) x-nativeSupportedDriftDivergence beta x) =
      (fun x => -nativeSupportedDriftDivergence beta x) := by
    funext x
    rw [coefficientValue_zero_one]
    exact zero_sub _
  have hAdj := nativeWeakConormalEndpoint_congr_coefficients _ _ (-beta)
    (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
    (fun x => coefficientValue 1 (0 : SmoothCoefficientJets 1) x-nativeSupportedDriftDivergence beta x)
    (fun x => -nativeSupportedDriftDivergence beta x) ha
    (memLp_referenceAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData p) hF rfl hNeg hMass
  have hAdjActual : nativeWeakConormalEndpoint (fun x => (a (p,x))ᵀ)
      (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
      (fun x => -nativeSupportedDriftDivergence beta x)
      (memLp_referenceAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData p) hF =
      referenceAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF p := by
    unfold referenceAdjointWeakConormalEndpointFamily
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
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_zero_one
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSupportedOriginalZeroEnergyL_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceOriginal_eq_adjoint_add_normal
