import Calderon.BoundedRadialDriftTrace
import Calderon.ActualNativeRadialFirstVariation
import Calderon.CurvatureContraction

/-! The actual/native first radial correction, with the same witnesses. L2
boundedness of the completed correction is separate from the core derivative
identities. The literature witnesses and every actual joint parameter are explicit. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory MvPolynomial
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem hasDerivAt_referenceOutwardRadialHarmonicLiftFamily_bounded_firstCorrection
    (hzero : SmoothBoundaryZeroClosure) (hcalc : FixedSobolevCalculus)
    (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (m : ℕ) (p : harmonicHomogeneous (m+1)) :
    HasDerivAt
      (fun r : ℝ => outwardRadialTraceL hcalc τ0
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r)
          (polynomialBallSobolev 2 p)))
      (radialDriftTraceL hF hO hD (referenceCenterDrift g L q y) (polynomialSphereL2 p)) 0 := by
  have hd := hasDerivAt_referenceOutwardRadialHarmonicLiftFamily_zero
    g L y0 Φ B ε C ρ H a w hData hzero hcalc hreg τ0
    q hq y hy (m+1) (by omega) p p.property.1 p.property.2
  rw [radialDriftTraceL_polynomial hF hO hD (referenceCenterDrift g L q y) m p]
  exact hd

theorem hasDerivAt_referenceOutwardRadialHarmonicLiftFamily_constant_firstCorrection
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (p : harmonicHomogeneous 0) :
    HasDerivAt
      (fun r : ℝ => outwardRadialTraceL hcalc τ0
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r)
          (polynomialBallSobolev 2 p)))
      (radialDriftTraceL hF hO hD (referenceCenterDrift g L q y) (polynomialSphereL2 p)) 0 := by
  have hdp : GreenRadialTrace.driftDerivative
      (polynomialCoordinateMap (referenceCenterDrift g L q y)) p = 0 := by
    simp only [GreenRadialTrace.driftDerivative,
      CurvatureContraction.pderiv_eq_zero_of_isHomogeneous_zero p p.property.1,
      mul_zero,Finset.sum_const_zero]
  have hd := hasDerivAt_referenceOutwardRadialHarmonicLiftFamily_polynomial_zero
    g L y0 Φ B ε C ρ H a w hData hcalc hreg τ0 q hq y hy p p.property.2
  have hT : radialDriftTraceL hF hO hD (referenceCenterDrift g L q y)
      (polynomialSphereL2 p) = 0 :=
    radialDriftTraceL_constant hF hO hD (referenceCenterDrift g L q y)
      ⟨polynomialSphereL2 p,polynomialSphereL2_mem 0 p p.property⟩
  rw [hT]
  have h0 : polynomialBallSobolev 0 (0 : MvPolynomial (Fin 3) ℝ) = 0 := by
    change polynomialBallSobolevLinearMap 0 0 = 0
    exact map_zero _
  simpa only [hdp,h0,map_zero] using hd

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
