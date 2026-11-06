import Calderon.ActualFiniteGaugeDensityFirstSection

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-FINITE-GAUGE-DENSITY-FIRST-SECTION-SUPPORT-UPFRONT-v001.md. Literal same-section support locality. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteHighHorizontalSection referenceFiniteGaugeAdjointMovingBoundaryFamily
  referenceHighDensityFirstAction referenceHighAdjointMovingBoundaryActionFamily
  referenceHighHorizontalAction sphereSobolevInclusionL sphereSobolevPartialSumL nativeThreeHalfCoefficientMulL
  referenceRadialEndpointInvertibleLocus referenceStrongDriftFamily

variable {KG KJ : Set (ℝ × (R3 × ℝ))}
  (G : ReferenceGaugeNormalReciprocalRoom g L Φ a KG)
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) KJ)

attribute [local irreducible] referenceFiniteGaugeDensityFirstSection
  NativeHarmonicLiftCompletion.nativeFiniteHarmonicProductHighRotationL referenceMetricGramFrame referenceFrameConnectionCoefficient

theorem tsupport_referenceFiniteGaugeDensityFirstSection_subset
    (n : ℕ) (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) (i : Fin 3) :
    tsupport (fun y => referenceFiniteGaugeDensityFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u y i) ⊆ tsupport u := by
  classical
  apply closure_minimal ?_ (isClosed_tsupport u)
  intro y hy
  by_contra hOutside
  have hValue : u y = 0 := image_eq_zero_of_notMem_tsupport hOutside
  have hDerivative : fderiv ℝ u y = 0 := fderiv_of_notMem_tsupport ℝ hOutside
  apply hy
  simp only [referenceFiniteGaugeDensityFirstSection, referenceFiniteHighHorizontalSection,
    hValue, hDerivative, ContinuousLinearMap.zero_apply, map_zero, smul_zero,
    Finset.sum_const_zero, add_zero]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tsupport_referenceFiniteGaugeDensityFirstSection_subset
