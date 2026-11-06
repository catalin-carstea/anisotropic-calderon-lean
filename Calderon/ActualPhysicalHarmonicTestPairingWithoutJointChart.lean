import Calderon.ActualNearBallPhysicalDensityPairing
import Calderon.NativeHighDensityTracePairingDictionary
import Calderon.ActualNativeSmoothHighHalfTraceCompatibility

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-PHYSICAL-HARMONIC-TEST-PAIRING-EXPANSION-v001.md. Same physical input in the dense trace core. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff ENNReal Topology InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic ConnectionError MetricVolume MetricOperator
  NativeH2ThreeHalfValueTrace NativeSmoothSharpTraceCompletion ActualNormalizedSecondMetricDrift ConformalDepth

theorem nativeThreeHalfValueTrace_half_eq_of_smoothSphereValue_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (f g : SmoothData) (hValue : smoothSphereValue f = smoothSphereValue g) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (smoothBallSobolev 2 f)) =
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (smoothBallSobolev 2 g)) := by
  have hHalf : smoothHalfTrace hF hO hD τ0 f = smoothHalfTrace hF hO hD τ0 g := by
    apply sphereSobolev_ext (1/2 : ℝ)
    intro k
    rw [sphereSobolevCoefficientL_smoothHalfTrace,sphereSobolevCoefficientL_smoothHalfTrace,
      τ0.valueTrace_smooth,τ0.valueTrace_smooth,hValue]
  exact (sphereSobolevInclusionL_nativeThreeHalfValueTraceL_smoothBallSobolev
    hcalc hF hO hD τ0 f).trans (hHalf.trans
      (sphereSobolevInclusionL_nativeThreeHalfValueTraceL_smoothBallSobolev hcalc hF hO hD τ0 g).symm)

theorem normalizedSecondLaplacian_congr_of_eventuallyEq
    (g1 g2 : MatrixField) (L q : ℝ) (u v : R3 → ℝ) (y : R3) (h : u =ᶠ[𝓝 y] v) :
    normalizedSecondLaplacian g1 g2 L q u y = normalizedSecondLaplacian g1 g2 L q v y := by
  have hFD : fderiv ℝ u =ᶠ[𝓝 y] fderiv ℝ v := h.fderiv
  have hGradient : gradient u =ᶠ[𝓝 y] gradient v := by
    filter_upwards [hFD] with x hx
    apply ext_inner_right ℝ
    intro W
    rw [inner_gradient_left,inner_gradient_left,hx]
  have hDiv : AngularPolynomial.densityWeightedDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
      (vol (dilatedMetric g2 q))
      (fun x => matrixOperatorMap ((dilatedMetric g2 q x)⁻¹) (gradient u x)) y =
      AngularPolynomial.densityWeightedDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
      (vol (dilatedMetric g2 q))
      (fun x => matrixOperatorMap ((dilatedMetric g2 q x)⁻¹) (gradient v x)) y := by
    unfold AngularPolynomial.densityWeightedDivergence
    apply Finset.sum_congr rfl
    intro i hi
    have hFlux : (fun x => vol (dilatedMetric g2 q) x *
        ⟪matrixOperatorMap ((dilatedMetric g2 q x)⁻¹) (gradient u x),
          EuclideanSpace.basisFun (Fin 3) ℝ i⟫_ℝ) =ᶠ[𝓝 y]
        (fun x => vol (dilatedMetric g2 q) x *
        ⟪matrixOperatorMap ((dilatedMetric g2 q x)⁻¹) (gradient v x),
          EuclideanSpace.basisFun (Fin 3) ℝ i⟫_ℝ) :=
      hGradient.mono (fun x hx => congrArg (fun t : R3 => vol (dilatedMetric g2 q) x *
        ⟪matrixOperatorMap ((dilatedMetric g2 q x)⁻¹) t,
          EuclideanSpace.basisFun (Fin 3) ℝ i⟫_ℝ) hx)
    exact congrArg (fun A : R3 →L[ℝ] ℝ => A (EuclideanSpace.basisFun (Fin 3) ℝ i)) hFlux.fderiv_eq
  unfold normalizedSecondLaplacian
  exact congrArg (fun a : ℝ => normalizedSecondLaplacianScalarJoint g1 g2 L (q,y) *
    (vol (dilatedMetric g2 q) y)⁻¹ * a) hDiv

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


attribute [local irreducible] referencePhysicalNativeThreeHalfTraceSection
  nativeThreeHalfValueTraceL smoothBallSobolev referencePhysicalPullbackData
  sphereSobolevInclusionL sphereSobolevDualPairing referencePhysicalDensityOperator normalizedSecondLaplacian

theorem referencePhysicalDensityOperator_pairing_physical_harmonic_neighborhood
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (y : R3) (hy : ‖y-y0‖ < 4*ρ) (hr : |R y| < 4*ρ) (hr0 : R y ≠ 0)
    (hyB : (y,0) ∈ B)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (S : Set R3) (hS : IsOpen S) (u : SmoothData)
    (hCover : (fun z => referenceFramedPhysicalEndpoint g L Φ (q,((y,R y),z))) ''
      closedBall (0 : R3) 1 ⊆ S)
    (hphysical : ∀ x ∈ S,
      coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u.1) x = 0)
    (ψ : R3 → SphereSobolev (3/2 : ℝ)) (hψ : ContDiff ℝ ∞ ψ) :
    R y * normalizedSecondLaplacian g g2 L q
      (fun x : R3 => sphereSobolevDualPairing (-(1/2 : ℝ))
        (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (ψ x))) (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) ((referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R u) x))) y =
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R ψ y) (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) ((referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R u) y)) := by
  obtain ⟨v,Y,hv,hY,hyY,hValue,hEquation⟩ :=
    exists_referencePhysicalDensityPairing_neighborhood_of_near_ball_harmonic
      g hg L y0 Φ B ε C ρ H a w hData g2 hg2 hcalc hreg hF hO hD τ0 hKernel
      q hq R hR y hy hr hr0 hyB hInv hp S hS u.1 u.2.contDiffOn hCover hphysical
  let U0 : R3 → SphereSobolev (3/2 : ℝ) := referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R u
  let U1 : R3 → SphereSobolev (3/2 : ℝ) := referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R v
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let f0 : R3 → ℝ := fun x => sphereSobolevDualPairing (-(1/2 : ℝ)) (J (I (ψ x))) (I (U0 x))
  let f1 : R3 → ℝ := fun x => sphereSobolevDualPairing (-(1/2 : ℝ)) (J (I (ψ x))) (I (U1 x))
  have hTrace : (fun x => I (U1 x)) =ᶠ[𝓝 y] (fun x => I (U0 x)) := by
    filter_upwards [hY.mem_nhds hyY] with z hz
    have hSphere : smoothSphereValue
        (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q z (R z) v) =
        smoothSphereValue (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q z (R z) u) := by
      ext x
      exact (hValue z hz x).trans
        (smoothSphereValue_referencePhysicalPullback_apply
          g hg L y0 Φ B hData.1.1.1 q z (R z) u x).symm
    have hNative := nativeThreeHalfValueTrace_half_eq_of_smoothSphereValue_eq hcalc hF hO hD τ0
      (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q z (R z) v)
      (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q z (R z) u) hSphere
    simpa only [U1,U0,I,referencePhysicalNativeThreeHalfTraceSection] using hNative
  have hScalar : f1 =ᶠ[𝓝 y] f0 := hTrace.mono (fun z hz => congrArg
    (fun t : SphereSobolev (1/2 : ℝ) => sphereSobolevDualPairing (-(1/2 : ℝ)) (J (I (ψ z))) t) hz)
  have hLeft := congrArg (fun a : ℝ => R y * a)
    (normalizedSecondLaplacian_congr_of_eventuallyEq g g2 L q f1 f0 y hScalar)
  have hRight := congrArg (fun t : SphereSobolev (1/2 : ℝ) =>
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R ψ y) t) hTrace.eq_of_nhds
  exact hLeft.symm.trans ((hEquation ψ hψ y hyY).trans hRight)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeThreeHalfValueTrace_half_eq_of_smoothSphereValue_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.normalizedSecondLaplacian_congr_of_eventuallyEq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensityOperator_pairing_physical_harmonic_neighborhood
