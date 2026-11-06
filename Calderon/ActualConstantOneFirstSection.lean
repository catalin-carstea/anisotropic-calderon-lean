import Calderon.ActualFiveHalfRegularMovingJets
import Calderon.ActualFiveHalfDensityFirstInRoom
import Calderon.ActualConstantOneFirstAngularLift
import Calderon.ActualConstantModeHorizontalIdentities
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

private lemma moving_constant_mode
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r c : ℝ) (moving leading degree correction remainder lifted regular : V)
    (hMoving : moving=r⁻¹ • leading+c • degree+correction+r • remainder)
    (hLeading : leading=lifted) (hDegree : degree=0)
    (hRegular : regular=correction+r • remainder) : moving=r⁻¹ • lifted+regular := by
  subst leading
  subst degree
  subst regular
  simpa only [smul_zero,add_zero,add_assoc] using hMoving

theorem referenceFiveHalfHorizontalAction_constantOne
    (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3) :
    referenceFiveHalfHorizontalAction g L q (fun _ => sphereSobolevConstantOne (5/2:ℝ)) y i=0 := by
  simp only [referenceFiveHalfHorizontalAction,referenceFiveHalfHorizontalAngularL,
    fderiv_const_apply,ContinuousLinearMap.zero_apply,map_zero,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    sphereSobolevRotationL_constantOne,smul_zero,Finset.sum_const_zero,add_zero]

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
attribute [local irreducible] harmonicSphereSubspace referenceFiveHalfDensityFirstActionInRoom
  referenceFiveHalfAdjointMovingBoundaryInRoom referenceFiveHalfConstantFirstRegularPartInRoom
  referenceNativeMovingAdjointParametricCorrection referenceFiveHalfAdjointMovingRegularRemainderInRoom
  sphereSobolevInclusionL sphereSobolevConstantOne constantOneFirstRaisingThreeHalf

theorem referenceFiveHalfDensityFirstActionInRoom_constantOne_native_decomposition
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (R : R3 → ℝ) (y : R3) (hy : ‖y-y0‖ ≤ ρ) (i : Fin 3)
    (hR : DifferentiableAt ℝ R y) (hr : R y ≠ 0)
    (hSegment : ∀ t ∈ uIcc (0:ℝ) (R y), (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceFiveHalfDensityFirstActionInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R (fun _ => sphereSobolevConstantOne (5/2:ℝ)) y i =
      (R y)⁻¹ • constantOneFirstRaisingThreeHalf hF i+
      referenceFiveHalfConstantFirstRegularPartInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 ((q,(y,R y)),fderiv ℝ R y) i := by
  have hMoving := referenceFiveHalfAdjointMovingBoundaryInRoom_native_decomposition_apply
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hg E hreg q hq R y hy i hR hr hSegment
    (sphereSobolevConstantOne (5/2:ℝ))
  have hLiteral : referenceFiveHalfDensityFirstActionInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R (fun _ => sphereSobolevConstantOne (5/2:ℝ)) y i =
      referenceFiveHalfAdjointMovingBoundaryInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 R (q,y) i (sphereSobolevConstantOne (5/2:ℝ)) := by
    simp only [referenceFiveHalfDensityFirstActionInRoom,referenceFiveHalfHorizontalAction_constantOne,zero_add]
  have hRegular : referenceFiveHalfConstantFirstRegularPartInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 ((q,(y,R y)),fderiv ℝ R y) i =
      sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (5/2:ℝ)
          ((q,y),fderiv ℝ R y) i (sphereSobolevConstantOne (5/2:ℝ))) +
      R y • referenceFiveHalfAdjointMovingRegularRemainderInRoom
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hg E ((q,(y,R y)),fderiv ℝ R y) i (sphereSobolevConstantOne (5/2:ℝ)) := by
    delta referenceFiveHalfConstantFirstRegularPartInRoom
    exact Eq.refl _
  have hSimple := moving_constant_mode (R y) (referenceRadiusHorizontalLogDerivative g L q R y i)
    (referenceFiveHalfAdjointMovingBoundaryInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 R (q,y) i (sphereSobolevConstantOne (5/2:ℝ)))
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (5/2:ℝ) i (sphereSobolevConstantOne (5/2:ℝ)))
    (sphereSobolevShiftedDegreeL (5/2:ℝ) (sphereSobolevConstantOne (5/2:ℝ)))
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (5/2:ℝ)
        ((q,y),fderiv ℝ R y) i (sphereSobolevConstantOne (5/2:ℝ))))
    (referenceFiveHalfAdjointMovingRegularRemainderInRoom
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hg E ((q,(y,R y)),fderiv ℝ R y) i (sphereSobolevConstantOne (5/2:ℝ)))
    (constantOneFirstRaisingThreeHalf hF i)
    (referenceFiveHalfConstantFirstRegularPartInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 ((q,(y,R y)),fderiv ℝ R y) i)
    hMoving (sphereSobolevAngularCoordinateTransposeL_constantOne_fivehalf hF hO hD i)
    (sphereSobolevShiftedDegreeL_constantOne (5/2:ℝ)) hRegular
  exact hLiteral.trans hSimple

theorem sphereSobolevInclusionL_constantOneFirstSection_eq_original
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (R : R3 → ℝ) (y : R3) (hy : ‖y-y0‖ ≤ ρ) (i : Fin 3)
    (hR : DifferentiableAt ℝ R y) (hr : R y ≠ 0)
    (hSegment : ∀ t ∈ uIcc (0:ℝ) (R y), (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hp : (q,(y,R y)) ∈ K)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      ((R y)⁻¹ • constantOneFirstRaisingThreeHalf hF i+
        referenceFiveHalfConstantFirstRegularPartInRoom
          g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 ((q,(y,R y)),fderiv ℝ R y) i) =
      referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun _ => sphereSobolevConstantOne (3/2:ℝ)) y i := by
  have hFirst := referenceFiveHalfDensityFirstActionInRoom_constantOne_native_decomposition
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg q hq R y hy i hR hr hSegment
  have hComp := referenceDensityFirstActionInRoom_fivehalf_threehalf_compatibility
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg q R
    (fun _ => sphereSobolevConstantOne (5/2:ℝ)) y i (differentiableAt_const _) hp hWeak
  have hField : (fun _ : R3 => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (sphereSobolevConstantOne (5/2:ℝ)))=(fun _ : R3 => sphereSobolevConstantOne (3/2:ℝ)) :=
    funext (fun _ => sphereSobolevInclusionL_constantOne (5/2:ℝ) (3/2:ℝ) (by norm_num))
  exact (congrArg (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) hFirst).symm.trans
    (hComp.trans (congrArg (fun uField : R3 → SphereSobolev (3/2:ℝ) =>
      referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R uField y i) hField))

theorem eventually_constantOneFirstSection_eq_original
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (y : R3) (i : Fin 3)
    (hRoom : ∀ᶠ z in 𝓝 y, ‖z-y0‖ ≤ ρ ∧ R z ≠ 0 ∧ (q,(z,R z)) ∈ K ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(z,R z))).IsInvertible ∧
      ∀ t ∈ uIcc (0:ℝ) (R z), (q,(z,t)) ∈
        referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (fun z => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      ((R z)⁻¹ • constantOneFirstRaisingThreeHalf hF i+
        referenceFiveHalfConstantFirstRegularPartInRoom
          g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 ((q,(z,R z)),fderiv ℝ R z) i)) =ᶠ[𝓝 y]
      (fun z => referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun _ => sphereSobolevConstantOne (3/2:ℝ)) z i) := by
  filter_upwards [hRoom] with z hz
  exact sphereSobolevInclusionL_constantOneFirstSection_eq_original
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg q hq R z hz.1 i
    (hR.differentiable (by simp) z) hz.2.1 hz.2.2.2.2 hz.2.2.1 hz.2.2.2.1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
