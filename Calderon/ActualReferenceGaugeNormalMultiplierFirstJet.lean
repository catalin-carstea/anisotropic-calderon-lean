import Calderon.ActualReferenceGaugeNormalSphereJet
import Calderon.NativeCoefficientMultiplierBoundaryDerivative
import Calderon.ActualReferenceGaugeNormalMultiplierInverse

/-! Upfront: general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION-native-boundary-multiplier-firstjet-v065.md. SAME actual alpha native
multipliers: zero is Id and radial derivative is spectral M_(c dot nu). -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  MetricVolume SphereHarmonic NativeCoefficientBoundaryMultiplier

variable (g : MatrixField) (L : ℝ)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (y0 : R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

theorem referenceGaugeNormalHalfMultiplierFamily_zero_radial_jet
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ) :
    referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,0)) =
        ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ)) ∧
    HasDerivAt (fun r : ℝ => referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r)))
        (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y)) 0 := by
  let Q : ℝ → SmoothCoefficientJets 2 := fun r => referenceGaugeNormalCoefficientJetsFamily
    g L Φ y0 B ε C ρ H a w hData hg 2 (q,(y,r))
  obtain ⟨hZero,hJet⟩ := referenceGaugeNormalSphereValueFamily_zero_radial_jet
    g L Φ y0 B ε C ρ H a w hData hg q hq y hy
  have hZeroNative : smoothSphereValue (coefficientSmoothData (Q 0)) = 1 := hZero
  have hJetNative : HasDerivAt (fun r => smoothSphereValue (coefficientSmoothData (Q r)))
      (∑ i : Fin 3, (referenceCenterDrift g L q y i) • sphereCoordinate i) 0 := hJet
  have hSlice : ContDiff ℝ ∞ (fun r : ℝ => (q,(y,r))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hActual : DifferentiableAt ℝ (fun r : ℝ => referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r))) 0 :=
    ((contDiff_referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0).comp hSlice).differentiable (by simp) 0
  have hNative : DifferentiableAt ℝ (fun r => nativeHalfCoefficientMulL hcalc hF hO hD τ0 (Q r)) 0 := hActual
  constructor
  · exact nativeHalfCoefficientMulL_eq_id_of_sphereValue_one hcalc hF hO hD τ0 (Q 0) hZeroNative
  · exact hasDerivAt_nativeHalfCoefficientMulL_of_boundary_jet hcalc hF hO hD τ0 Q
      (referenceCenterDrift g L q y) hNative hJetNative

theorem referenceGaugeNormalNegativeHalfMultiplierFamily_zero_radial_jet
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ) :
    referenceGaugeNormalNegativeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,0)) =
        ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2 : ℝ))) ∧
    HasDerivAt (fun r : ℝ => referenceGaugeNormalNegativeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r)))
        (sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (referenceCenterDrift g L q y)) 0 := by
  let Q : ℝ → SmoothCoefficientJets 2 := fun r => referenceGaugeNormalCoefficientJetsFamily
    g L Φ y0 B ε C ρ H a w hData hg 2 (q,(y,r))
  obtain ⟨hZero,hJet⟩ := referenceGaugeNormalSphereValueFamily_zero_radial_jet
    g L Φ y0 B ε C ρ H a w hData hg q hq y hy
  have hZeroNative : smoothSphereValue (coefficientSmoothData (Q 0)) = 1 := hZero
  have hJetNative : HasDerivAt (fun r => smoothSphereValue (coefficientSmoothData (Q r)))
      (∑ i : Fin 3, (referenceCenterDrift g L q y i) • sphereCoordinate i) 0 := hJet
  have hSlice : ContDiff ℝ ∞ (fun r : ℝ => (q,(y,r))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hActual : DifferentiableAt ℝ (fun r : ℝ => referenceGaugeNormalNegativeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r))) 0 :=
    ((contDiff_referenceGaugeNormalNegativeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0).comp hSlice).differentiable (by simp) 0
  have hNative : DifferentiableAt ℝ (fun r => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (Q r)) 0 := hActual
  constructor
  · exact nativeNegativeHalfCoefficientMulL_eq_id_of_sphereValue_one hcalc hF hO hD τ0 (Q 0) hZeroNative
  · exact hasDerivAt_nativeNegativeHalfCoefficientMulL_of_boundary_jet hcalc hF hO hD τ0 Q
      (referenceCenterDrift g L q y) hNative hJetNative

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalHalfMultiplierFamily_zero_radial_jet
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalNegativeHalfMultiplierFamily_zero_radial_jet
