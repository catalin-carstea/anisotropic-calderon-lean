import Calderon.ActualReferenceRotationConormalCompatibility
import Calderon.ActualReferenceRotationLowerRadialEndpoint
import Calderon.ActualReferenceOrthogonalSharpUpperEndpoint

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeFullSharpHalfTrace NativeFullHalfRadialTrace SmoothSphereRotation

lemma nativeHalfOutwardTraceL_negative_inclusion
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (U : BallSobolev 2) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (nativeHalfOutwardTraceL hF hO hD hcalc τ0 U) =
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0 U)) := by
  have ht := congrArg (fun A : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      A (nativeHalfOutwardTraceL hF hO hD hcalc τ0 U))
    (sphereSobolevInclusionL_trans (1/2:ℝ) 0 (-(1/2:ℝ)) (by norm_num) (by norm_num))
  exact ht.symm.trans (congrArg (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL_nativeHalfOutwardTraceL hF hO hD hcalc τ0 U))

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


lemma referenceRotationLowerRadialEndpointFamily_inclusion_eq_coarse_radial
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    referenceRotationLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0
        (referenceOrthogonalStrongHarmonicLift g L y0 Φ B ε C ρ H a w hData
          hcalc hF (coordinateRotationIsometry i j θ) p f))) := by
  have hb := nativeHalfTraceL_referenceOrthogonalStrongHarmonicLift
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (coordinateRotationIsometry i j θ) p hStrong f
  have hc := referenceRotationWeakConormalEndpointFamily_inclusion_eq_conormal
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j θ p hStrong hWeak f
  have hn := referenceRotationNormalBoundaryMultiplierFamily_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j θ p hNormal
  rw [referenceRotationLowerRadialEndpointFamily_apply]
  exact nativeCoefficient_boundary_radial_conversion_of_isInvertible hcalc hF hO hD τ0
    (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j (θ,p))
    (referenceRotationNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j (θ,p))
    (fun l => referenceRotationTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j l (θ,p))
    (coefficientSmoothData_referenceRotationNormalJets_eq_boundaryData
      g L y0 Φ B ε C ρ H a w hData i j (θ,p))
    (fun l => coefficientSmoothData_referenceRotationTangentJets_eq_boundaryData
      g L y0 Φ B ε C ρ H a w hData i j l (θ,p)) hn _ _ _ hb hc

lemma referenceRotationLowerRadialEndpointFamily_upper_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    referenceRotationLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (referenceOrthogonalSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 (coordinateRotationIsometry i j θ) p f) := by
  have hc := referenceRotationLowerRadialEndpointFamily_inclusion_eq_coarse_radial
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j θ p hNormal hStrong hWeak f
  rw [referenceOrthogonalSharpRadialTraceFamily_eq_actual_outward_trace]
  exact hc.trans (nativeHalfOutwardTraceL_negative_inclusion hcalc hF hO hD τ0 _).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfOutwardTraceL_negative_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationLowerRadialEndpointFamily_inclusion_eq_coarse_radial
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationLowerRadialEndpointFamily_upper_compatibility
