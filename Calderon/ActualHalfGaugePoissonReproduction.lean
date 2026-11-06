import Calderon.ActualHalfGaugeHarmonicEvaluation
import Calderon.ActualHalfGaugeNativeHarmonicPairing
import Calderon.ActualReferenceSmoothHarmonicity
import Calderon.FlatHarmonicMeasureUniqueness
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily DirichletFamily.DriftBootstrap
  NativePolynomialBulkMoments SphereHarmonic NativeH2ThreeHalfValueTrace
  MixedKernelConstructionTask
attribute [local irreducible] referencePhysicalHalfGaugeConormalDensity referencePhysicalHalfGaugeCollarForcing
  referencePhysicalGaugeCoefficientJets ordinaryPrincipalL sphereSobolevInclusionL sphereSobolevZeroEquiv

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0)
    (η : R3 → ℝ) (hη : ContDiff ℝ ∞ η)


include hg hData hcalc in
theorem referencePhysicalHalfGaugeConormalDensity_reproduces_smooth
    (hreg : FixedDirichletRegularity)
    (hθOne : ∀ z ∈ ball (0 : R3) 1, θ z = 1)
    (hζOne : ∀ z ∉ closedBall (0 : R3) (1/2), ζ z = 1)
    (hηZero : ∀ z ∈ closedBall (0 : R3) (1/2), η z = 0)
    (hηSphere : ∀ x : UnitSphere, η x.val = 1)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (u : SmoothData)
    (hHarm : ∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
      (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x)) (gradient u.1 x)) z = 0) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0 (q,(y,r)))),
      τ0.valueTraceL (smoothSobolev u)⟫_ℝ = u.1 0 := by
  have hOp := ordinaryPrincipalL_referencePhysicalGauge_smooth_eq_zero g hg L y0 Φ B ε C ρ H a w hData hcalc q y r u hHarm
  have hPair := referencePhysicalHalfGaugeConormalDensity_harmonic_valueTrace_pairing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη
    hreg (1/2) hθOne hζOne hηZero hηSphere hF hO hD τ0 q hq y hy r hr (smoothBallSobolev 2 u) hOp
  rw [firstOrder_smoothBallSobolev] at hPair
  exact hPair.trans (referencePhysicalHalfGaugeCollarForcing_harmonic_inner g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero hθOne hζOne q hq y hy r hr u hHarm).symm

include hg hData hcalc in
theorem referencePhysicalHalfGaugeConormalDensity_reproduces_native_harmonic_smooth
    (hreg : FixedDirichletRegularity)
    (hθOne : ∀ z ∈ ball (0 : R3) 1, θ z = 1)
    (hζOne : ∀ z ∉ closedBall (0 : R3) (1/2), ζ z = 1)
    (hηZero : ∀ z ∈ closedBall (0 : R3) (1/2), η z = 0)
    (hηSphere : ∀ x : UnitSphere, η x.val = 1)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (u : SmoothData)
    (hP : ordinaryPrincipalL hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))) (smoothBallSobolev 2 u) = 0) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0 (q,(y,r)))),
      τ0.valueTraceL (smoothSobolev u)⟫_ℝ = u.1 0 := by
  exact referencePhysicalHalfGaugeConormalDensity_reproduces_smooth g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη
    hreg hθOne hζOne hηZero hηSphere hF hO hD τ0 q hq y hy r hr u
    (referencePhysicalGauge_flux_harmonic_of_ordinaryPrincipalL_zero g hg L y0 Φ B ε C ρ H a w hData hcalc q y r u hP)

include hg hData hcalc in
theorem referencePhysicalHalfGaugeConormalDensity_reproduces_nativeTrace
    (hreg : FixedDirichletRegularity)
    (hθOne : ∀ z ∈ ball (0 : R3) 1, θ z = 1)
    (hζOne : ∀ z ∉ closedBall (0 : R3) (1/2), ζ z = 1)
    (hηZero : ∀ z ∈ closedBall (0 : R3) (1/2), η z = 0)
    (hηSphere : ∀ x : UnitSphere, η x.val = 1)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (u : SmoothData)
    (hP : ordinaryPrincipalL hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))) (smoothBallSobolev 2 u) = 0) :
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0 (q,(y,r)))))
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (smoothBallSobolev 2 u))) = u.1 0 := by
  rw [nativeThreeHalfTrace_dualPairing_eq_L2_valueTrace hcalc hF hO hD τ0 (referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0 (q,(y,r))) u]
  exact referencePhysicalHalfGaugeConormalDensity_reproduces_native_harmonic_smooth g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη
    hreg hθOne hζOne hηZero hηSphere hF hO hD τ0 q hq y hy r hr u hP

include hg hData hcalc in
theorem referencePhysicalHalfGaugeConormalDensity_radius_zero_eq_one
    (hreg : FixedDirichletRegularity)
    (hθOne : ∀ z ∈ ball (0 : R3) 1, θ z = 1)
    (hζOne : ∀ z ∉ closedBall (0 : R3) (1/2), ζ z = 1)
    (hηZero : ∀ z ∈ closedBall (0 : R3) (1/2), η z = 0)
    (hηSphere : ∀ x : UnitSphere, η x.val = 1)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
 :
    referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0 (q,(y,0)) =
      sphereSobolevSingleL (3/2 : ℝ) 0
        ⟨polynomialSphereL2 (MvPolynomial.C 1),polynomialSphereL2_mem 0 _ (C_harmonicHomogeneous 1)⟩ := by
  apply sphereSobolev_eq_one_of_euclideanHarmonic_reproduces hO hD τ0
  intro u hu
  have hr0 : |(0 : ℝ)| ≤ 4*ρ := by
    rw [abs_zero]
    exact mul_nonneg (by norm_num) hData.1.2.1.le
  exact referencePhysicalHalfGaugeConormalDensity_reproduces_smooth g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη
    hreg hθOne hζOne hηZero hηSphere hF hO hD τ0 q hq y hy 0 hr0 u
    (referencePhysicalGauge_radius_zero_harmonic_of_euclideanHarmonic g hg L y0 Φ B ε C ρ H a w hData q hq y hy u hu)

end OAI.AnisotropicCalderon.ConnectionError
