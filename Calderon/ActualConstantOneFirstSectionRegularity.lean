import Calderon.ActualFiveHalfRegularMovingJets
import Calderon.ActualConstantOneFirstAngularLift
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) {K : Set (ℝ × (R3 × ℝ))}
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) K)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
attribute [local irreducible] harmonicSphereSubspace
  referenceFiveHalfAdjointMovingBoundaryInRoom referenceFiveHalfConstantFirstRegularPartInRoom
  referenceNativeMovingAdjointParametricCorrection referenceFiveHalfAdjointMovingRegularRemainderInRoom
  sphereSobolevInclusionL sphereSobolevConstantOne constantOneFirstRaisingThreeHalf

theorem contDiffAt_constantOneFirstSection
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (y : R3) (i : Fin 3) (hr : R y ≠ 0)
    (hSegment : ∀ t ∈ uIcc (0:ℝ) (R y), (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun z => (R z)⁻¹ • constantOneFirstRaisingThreeHalf hF i+
      referenceFiveHalfConstantFirstRegularPartInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 ((q,(z,R z)),fderiv ℝ R z) i) y := by
  have hSegmentTheta (theta : ℝ) (htheta : theta ∈ Icc (0:ℝ) 1) :
      (q,(y,theta*R y)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
    apply hSegment
    rcases le_total 0 (R y) with hp | hn
    · rw [uIcc_of_le hp]
      exact ⟨mul_nonneg htheta.1 hp,
        (mul_le_mul_of_nonneg_right htheta.2 hp).trans_eq (one_mul _)⟩
    · rw [uIcc_of_ge hn]
      exact ⟨by simpa only [one_mul] using mul_le_mul_of_nonpos_right htheta.2 hn,
        mul_nonpos_of_nonneg_of_nonpos htheta.1 hn⟩
  have hDR : ContDiffAt ℝ ∞ (fderiv ℝ R) y :=
    (hR.fderiv_right (m := ∞) (by simp)).contDiffAt
  have hGraph : ContDiffAt ℝ ∞ (fun z : R3 => ((q,(z,R z)),fderiv ℝ R z)) y :=
    ((contDiffAt_const.prodMk (contDiffAt_id.prodMk hR.contDiffAt)).prodMk hDR)
  have hK : ContDiffAt ℝ ∞
      (fun t : (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ) => referenceFiveHalfConstantFirstRegularPartInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 t i) ((q,(y,R y)),fderiv ℝ R y) :=
    contDiffAt_referenceFiveHalfConstantFirstRegularPartInRoom_of_segment
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg ((q,(y,R y)),fderiv ℝ R y) i hSegmentTheta
  have hPull : ContDiffAt ℝ ∞ (fun z => referenceFiveHalfConstantFirstRegularPartInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 ((q,(z,R z)),fderiv ℝ R z) i) y := by
    simpa only [Function.comp_def] using
      hK.comp (f := fun z : R3 => ((q,(z,R z)),fderiv ℝ R z)) y hGraph
  have hV : ContDiffAt ℝ ∞ (fun z : R3 => (R z)⁻¹ • constantOneFirstRaisingThreeHalf hF i) y :=
    (hR.contDiffAt.inv hr).smul contDiffAt_const
  exact hV.add hPull

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
