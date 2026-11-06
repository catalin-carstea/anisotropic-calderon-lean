import Calderon.ActualLowerAdjointCoordinateActualJetTaylor
import Calderon.MovingAdjointTaylorQuotientAlgebra
import Calderon.ActualNativeMovingLocalRemainder
import Calderon.ActualFinitePairedRadialQuarticDomain

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier

attribute [local irreducible] referenceLowerAdjointMovingDifferenceQuotient
  referenceLowerAdjointMovingBoundaryActionFamily referenceLowerAdjointMovingBoundaryAction
  referenceLowerAdjointJacobiBoundaryCorrection referenceAdjointHalfRadialFamily
  referenceLowerAdjointCoordinateBoundaryFamily referenceRadialEndpointInvertibleLocus
  secondTaylorRemainder sphereSobolevAngularCoordinateTransposeL
  sphereSobolevLinearCoordinateMulL

lemma referenceLowerAdjointMovingDifferenceQuotient_eq_ordered_words
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (i : Fin 3) (hr : R y ≠ 0)
    (hInv : ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)
    (hSegment : ∀ t ∈ uIcc (0 : ℝ) (R y), (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let r : ℝ := R y
    let f : ℝ := referenceRadiusHorizontalLogDerivative g L q R y i
    let A : ℝ → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun t =>
      referenceAdjointHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
    let T := secondTaylorRemainder A r
    let D := deriv A 0
    let C0 : Fin 3 → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun j =>
      referenceLowerAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
    let M : Fin 3 → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun j =>
      sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)
    let N : Fin 3 → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun j =>
      nativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)
    referenceLowerAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i =
      T.comp (M i) + (∑ j : Fin 3, (C0 j).comp (N j)) +
      r • (∑ j : Fin 3, D.comp ((M j).comp (N j))) +
      r^2 • (∑ j : Fin 3, T.comp ((M j).comp (N j))) + (r*f) • T := by
  intro r f A T D C0 M N
  have hEndpoint := hSegment (R y) (right_mem_uIcc : R y ∈ uIcc (0 : ℝ) (R y))
  unfold referenceRadialEndpointInvertibleLocus at hEndpoint
  have hFamily := referenceLowerAdjointMovingBoundaryActionFamily_eq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i hInv hEndpoint.2.1
  have hZero (j : Fin 3) : C0 j = sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j :=
    referenceLowerAdjointCoordinateBoundaryFamily_zero_eq_angularTranspose
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy j
  have hCoordinate (j : Fin 3) :
      referenceLowerAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j =
      C0 j + r • D.comp (M j) + r^2 • T.comp (M j) :=
    referenceLowerAdjointCoordinateBoundaryFamily_signed_actual_jet_taylor
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy r j hSegment
  have hRadialFirst : D =
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ)
          (referenceCenterDrift g L q y)) :=
    deriv_referenceAdjointHalfRadialFamily_zero_eq_nativeFirstCorrection
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hNativeTaylor := referenceAdjointHalfRadialFamily_signed_native_taylor
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy r hSegment
  have hActualTaylor : A r = sphereSobolevShiftedDegreeL (1/2 : ℝ) + r • D + r^2 • T :=
    hNativeTaylor.trans (congrArg
      (fun F : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
        sphereSobolevShiftedDegreeL (1/2 : ℝ) + r • F + r^2 • T) hRadialFirst.symm)
  have hCoordinateFirst := deriv_referenceLowerAdjointCoordinateBoundaryFamily_zero_eq_nativeFirstCorrection
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i
  have hFirstAsRadial :
      deriv (fun t : ℝ => referenceLowerAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t)) i) 0 = D.comp (M i) := by
    apply ContinuousLinearMap.ext
    intro v
    have hC := congrArg (fun F : SphereSobolev (1/2 : ℝ) →L[ℝ]
      SphereSobolev (-(1/2 : ℝ)) => F v) hCoordinateFirst
    have hD := congrArg (fun F : SphereSobolev (1/2 : ℝ) →L[ℝ]
      SphereSobolev (-(1/2 : ℝ)) => F (M i v)) hRadialFirst
    simpa only [ContinuousLinearMap.comp_apply,M] using hC.trans hD.symm
  have hCombined := referenceLowerAdjointMoving_firstJet_eq_nativeParametricCorrection
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy R hR hr i
  have hNativeBase :
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
          ((q,y),fderiv ℝ R y) i) = D.comp (M i) + (r*f) • D :=
    hCombined.symm.trans (congrArg
      (fun C : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => C + (r*f) • D)
      hFirstAsRadial)
  apply ContinuousLinearMap.ext
  intro u
  have hJac : referenceLowerAdjointJacobiBoundaryCorrection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r i hInv u =
      (∑ j : Fin 3, C0 j (N j u)) + r • (∑ j : Fin 3, D (M j (N j u))) +
      r^2 • (∑ j : Fin 3, T (M j (N j u))) := by
    simp only [referenceLowerAdjointJacobiBoundaryCorrection,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
    change (∑ j : Fin 3, referenceLowerAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j (N j u)) = _
    calc
      _ = ∑ j : Fin 3, (C0 j (N j u) + r • D (M j (N j u)) +
          r^2 • T (M j (N j u))) := by
        apply Finset.sum_congr rfl
        intro j hj
        have h := congrArg (fun F : SphereSobolev (1/2 : ℝ) →L[ℝ]
          SphereSobolev (-(1/2 : ℝ)) => F (N j u)) (hCoordinate j)
        simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.comp_apply] using h
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.smul_sum]
  have hCPoint := congrArg (fun F : SphereSobolev (1/2 : ℝ) →L[ℝ]
    SphereSobolev (-(1/2 : ℝ)) => F u) (hCoordinate i)
  have hAPoint := congrArg (fun F : SphereSobolev (1/2 : ℝ) →L[ℝ]
    SphereSobolev (-(1/2 : ℝ)) => F u) hActualTaylor
  have hBasePoint := congrArg (fun F : SphereSobolev (1/2 : ℝ) →L[ℝ]
    SphereSobolev (-(1/2 : ℝ)) => F u) hNativeBase
  have hZeroPoint := congrArg (fun F : SphereSobolev (1/2 : ℝ) →L[ℝ]
    SphereSobolev (-(1/2 : ℝ)) => F u) (hZero i).symm
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply] at hCPoint hAPoint hBasePoint
  have hMoving := congrArg (fun F : SphereSobolev (1/2 : ℝ) →L[ℝ]
    SphereSobolev (-(1/2 : ℝ)) => F u) hFamily
  simp only [referenceLowerAdjointMovingBoundaryAction,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply] at hMoving
  have hMovingSubstitution := congrArg₂
    (fun z t : SphereSobolev (-(1/2 : ℝ)) => z+t)
    (congrArg₂ (fun z t : SphereSobolev (-(1/2 : ℝ)) => z+t)
      (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => r⁻¹ • z) hCPoint)
      (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => r • z) hJac))
    (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => f • z) hAPoint)
  have hMovingExpanded := hMoving.trans hMovingSubstitution
  have hBaseExpanded := congrArg₂
    (fun z t : SphereSobolev (-(1/2 : ℝ)) =>
      r⁻¹ • z + f • sphereSobolevShiftedDegreeL (1/2 : ℝ) u + t)
    hZeroPoint hBasePoint
  have hDifference := congrArg₂
    (fun z t : SphereSobolev (-(1/2 : ℝ)) => z-t) hMovingExpanded hBaseExpanded
  have hScaled := congrArg
    (fun z : SphereSobolev (-(1/2 : ℝ)) => r⁻¹ • z) hDifference
  have hAlgebra := inv_smul_moving_taylor_sub_first_order r f
    (C0 i u) (D (M i u)) (T (M i u))
    (∑ j : Fin 3, C0 j (N j u)) (∑ j : Fin 3, D (M j (N j u)))
    (∑ j : Fin 3, T (M j (N j u)))
    (sphereSobolevShiftedDegreeL (1/2 : ℝ) u) (D u) (T u) hr
  have hComplete : referenceLowerAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i u =
      T (M i u) + (∑ j : Fin 3, C0 j (N j u)) +
      r • (∑ j : Fin 3, D (M j (N j u))) +
      r^2 • (∑ j : Fin 3, T (M j (N j u))) + (r*f) • T u := by
    simp only [referenceLowerAdjointMovingDifferenceQuotient,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply]
    change r⁻¹ • (referenceLowerAdjointMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i u -
      (r⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i u +
        f • sphereSobolevShiftedDegreeL (1/2 : ℝ) u +
        (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num))
          (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
            ((q,y),fderiv ℝ R y) i u))) = _
    exact hScaled.trans hAlgebra
  simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply] using hComplete

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerAdjointMovingDifferenceQuotient_eq_ordered_words
