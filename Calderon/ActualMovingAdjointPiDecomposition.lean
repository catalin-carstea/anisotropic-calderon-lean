import Calderon.ActualHighAdjointWeightedCorrectionPointwiseIdentity
import Calderon.RadiusSquaredFiveTermVectorCancellation
import Calderon.ActualOriginalPiRadialCoefficientCaps

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

private instance movingPiDecompositionHalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

private instance movingPiDecompositionOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by
  infer_instance

private instance movingPiDecompositionIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

private instance movingPiDecompositionEndIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

attribute [local irreducible] referenceHighAdjointMovingDifferenceQuotient
  referenceAdjointThreeHalfRadialFamily referenceHighAdjointCoordinateBoundaryFamily
  referenceRadialEndpointInvertibleLocus secondTaylorRemainder
  nativeThreeHalfCoefficientMulL referenceJacobiBoundaryThreeHalfCoefficientFamily
  sphereSobolevLinearCoordinateMulL referenceRadiusHorizontalLogDerivative

private lemma moving_adjoint_quotient_ordered_sum
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (y : R3) (hy : y ∈ closedBall y0 ρ)
    (hr : R y ≠ 0)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hInv : ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)
    (i : Fin 3) :
    let T := secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) (R y)
    let N : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun j =>
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryThreeHalfCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j (q,(y,R y)))
    let C0 : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun j =>
      referenceHighAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
    let D := deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0
    let M : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun j =>
      sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)
    let f := referenceRadiusHorizontalLogDerivative g L q R y i
    ∀ u : SphereSobolev (3/2 : ℝ),
      referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i u =
      T (M i u)+(∑ j : Fin 3, C0 j (N j u))+
        R y • (∑ j : Fin 3, D (M j (N j u)))+
        (R y)^2 • (∑ j : Fin 3, T (M j (N j u)))+(R y*f) • T u := by
  intro T N C0 D M f u
  have hSquarePackage :=
    referenceHighAdjointMovingDifferenceQuotient_sq_smul_eqOn_ordered_extension
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hSquare := hSquarePackage i (x := y) ⟨hy,hr,hSegment,hInv⟩
  have hValue := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A u) hSquare
  have hValueTyped : (R y)^2 • referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i u =
      (R y)^2 • T (M i u)+(∑ j : Fin 3, (R y)^2 • C0 j (N j u))+
        (∑ j : Fin 3, (R y)^3 • D (M j (N j u)))+
        (∑ j : Fin 3, ((R y)^2*(R y)^2) • T (M j (N j u)))+
        (f*(R y)^3) • T u := by
    simpa only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_smul,smul_smul]
      using hValue
  exact eq_ordered_five_term_vector_sum_of_sq_eq (R y) f
    (referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i u)
    (T (M i u)) (T u) (fun j => C0 j (N j u))
    (fun j => D (M j (N j u))) (fun j => T (M j (N j u))) hr hValueTyped


theorem referenceHighAdjointMovingDifferenceQuotient_eq_originalPi_radial_add_first_order
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (y : R3) (hy : y ∈ closedBall y0 ρ)
    (hr : R y ≠ 0)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hInv : ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)
    (i : Fin 3) :
    let T := secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) (R y)
    let N : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun j =>
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryThreeHalfCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j (q,(y,R y)))
    let C0 : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun j =>
      referenceHighAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
    let D := deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0
    let M : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun j =>
      sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)
    let f := referenceRadiusHorizontalLogDerivative g L q R y i
    ∀ u : SphereSobolev (3/2 : ℝ),
      referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i u =
        referenceOriginalPiAdjointRadialCoefficient
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i
          ((q,(y,R y)),fderiv ℝ R y) u +
        (∑ j : Fin 3, C0 j (N j u)) + R y • (∑ j : Fin 3, D (M j (N j u))) := by
  intro T N C0 D M f u
  have hOrdered : referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i u =
      T (M i u)+(∑ j : Fin 3, C0 j (N j u))+
        R y • (∑ j : Fin 3, D (M j (N j u)))+
        (R y)^2 • (∑ j : Fin 3, T (M j (N j u)))+(R y*f) • T u :=
    moving_adjoint_quotient_ordered_sum
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR y hy hr hSegment hInv i u
  have hScalar : R y*f = fderiv ℝ R y
      (conformalReferenceGramFrameOperatorJoint g L (q,y) (EuclideanSpace.single i 1)) :=
    referenceRadius_mul_horizontalLogDerivative_eq_fderiv g L q R hR y hr i
  have hPi : referencePiThreeHalfMultiplier
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i
      ((q,(y,R y)),fderiv ℝ R y) u =
      M i u+(R y)^2 • (∑ j : Fin 3, M j (N j u))+(R y*f) • u := by
    unfold referencePiThreeHalfMultiplier
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply]
    change M i u+(R y)^2 • (∑ j : Fin 3, M j (N j u))+
      fderiv ℝ R y (conformalReferenceGramFrameOperatorJoint g L (q,y) (EuclideanSpace.single i 1)) • u = _
    exact congrArg (fun c : ℝ => M i u+(R y)^2 • (∑ j : Fin 3, M j (N j u))+c • u) hScalar.symm
  have hFold : referenceOriginalPiAdjointRadialCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i
      ((q,(y,R y)),fderiv ℝ R y) u =
      T (M i u)+(R y)^2 • (∑ j : Fin 3, T (M j (N j u)))+(R y*f) • T u := by
    unfold referenceOriginalPiAdjointRadialCoefficient
    change T (referencePiThreeHalfMultiplier
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i
      ((q,(y,R y)),fderiv ℝ R y) u) = _
    exact (congrArg T hPi).trans (by simp only [map_add,map_smul,map_sum])
  have reorder {Z : Type} [AddCommGroup Z] (a b c d e : Z) :
      a+b+c+d+e = (a+d+e)+b+c := by abel
  exact hOrdered.trans ((reorder (T (M i u)) (∑ j : Fin 3, C0 j (N j u))
    (R y • (∑ j : Fin 3, D (M j (N j u))))
    ((R y)^2 • (∑ j : Fin 3, T (M j (N j u)))) ((R y*f) • T u)).trans
      (congrArg (fun z : SphereSobolev (1/2 : ℝ) =>
        z+(∑ j : Fin 3, C0 j (N j u))+R y • (∑ j : Fin 3, D (M j (N j u)))) hFold.symm))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingDifferenceQuotient_eq_originalPi_radial_add_first_order
