import Calderon.ActualAdjointMovingBoundaryAction
import Calderon.NativeHalfCoefficientRotationDualAdjunction
import Calderon.ActualReferenceAdjointHalfRadialDuality

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.SphereHarmonic

attribute [local irreducible] sphereSobolevRadialDriftL

theorem sphereSobolevDualPairing_linearCoordinate_half_duality
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (d : R3)
    (u : SphereSobolev (-(1/2 : ℝ))) (v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) v
      (sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) d u) =
    sphereSobolevDualPairing (1/2 : ℝ)
      (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) d v) u := by
  let A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) d
  let B : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevRadialDriftL hF hO hD (-(1/2 : ℝ)) d
  have hIndex :
      (sphereSobolevRadialDriftL hF hO hD (-(-(1/2 : ℝ))) d :
        SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) =
      sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) d := by
    have hEqualIndex (a b : ℝ) (hab : a = b) :
        (sphereSobolevRadialDriftL hF hO hD a d :
          SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) =
        (sphereSobolevRadialDriftL hF hO hD b d :
          SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by
      cases hab
      rfl
    exact hEqualIndex (-(-(1/2 : ℝ))) (1/2 : ℝ) (neg_neg (1/2 : ℝ))
  have hA : ⟪v,ContinuousLinearMap.adjoint A u⟫_ℝ = ⟪A v,u⟫_ℝ :=
    ContinuousLinearMap.adjoint_inner_right A v u
  have hB : ⟪ContinuousLinearMap.adjoint B v,u⟫_ℝ = ⟪v,B u⟫_ℝ :=
    ContinuousLinearMap.adjoint_inner_left B u v
  have hCombined : -⟪v,B u⟫_ℝ - ⟪v,ContinuousLinearMap.adjoint A u⟫_ℝ =
      -⟪A v,u⟫_ℝ - ⟪ContinuousLinearMap.adjoint B v,u⟫_ℝ := by
    calc
      _ = -⟪ContinuousLinearMap.adjoint B v,u⟫_ℝ - ⟪A v,u⟫_ℝ :=
        congrArg₂ (fun x y : ℝ => -x-y) hB.symm hA
      _ = _ := by ring
  simpa only [sphereSobolevDualPairing,sphereSobolevLinearCoordinateMulL,
    sphereSobolevRadialDriftAdjointL,hIndex,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply,inner_sub_right,inner_neg_right,
    inner_sub_left,inner_neg_left,A,B] using hCombined

end OAI.AnisotropicCalderon.SphereHarmonic
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier

attribute [local irreducible] referenceJacobiBoundaryCoefficientJets
  referenceLowerRadialEndpointFamily referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem sphereSobolevDualPairing_referenceLowerCoordinateBoundary_adjoint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (u v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) v
      (referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i u) =
    sphereSobolevDualPairing (1/2 : ℝ) u
      (referenceLowerAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i v) := by
  have hTerm (j : Fin 3) :
      ⟪v,sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ))
        (EuclideanSpace.single j 1) (sphereSobolevRotationL (1/2 : ℝ) j i u)⟫_ℝ =
      -⟪u,sphereSobolevRotationL (1/2 : ℝ) j i
        (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
          (EuclideanSpace.single j 1) v)⟫_ℝ := by
    have hM := sphereSobolevDualPairing_linearCoordinate_half_duality hF hO hD
      (EuclideanSpace.single j 1) (sphereSobolevRotationL (1/2 : ℝ) j i u) v
    have hSwap :
        ⟪sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
          (EuclideanSpace.single j 1) v,sphereSobolevRotationL (1/2 : ℝ) j i u⟫_ℝ =
        ⟪sphereSobolevRotationL (1/2 : ℝ) j i u,
          sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
            (EuclideanSpace.single j 1) v⟫_ℝ := real_inner_comm _ _
    exact hM.trans (hSwap.trans (sphereSobolevDualPairing_half_rotation_skew j i u
      (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1) v)))
  have hTang :
      ⟪v,sphereTangentialDerivativeL hF hO hD i u⟫_ℝ =
      ⟪u,-∑ j : Fin 3, sphereSobolevRotationL (1/2 : ℝ) j i
        (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
          (EuclideanSpace.single j 1) v)⟫_ℝ := by
    simp only [sphereTangentialDerivativeL,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply,sphereSobolevLinearCoordinateMulL_negative_half_notation_eq,
      inner_sum,inner_neg_right]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j hj => hTerm j)
  have hRad :
      ⟪v,sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ))
        (EuclideanSpace.single i 1) (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p u)⟫_ℝ =
      ⟪u,referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
          (EuclideanSpace.single i 1) v)⟫_ℝ := by
    exact (sphereSobolevDualPairing_linearCoordinate_half_duality hF hO hD
      (EuclideanSpace.single i 1) (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p u) v).trans
      (sphereSobolevDualPairing_referenceLowerRadial_adjoint
        g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD p hWeak u
          (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1) v))
  change ⟪v,referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i u⟫_ℝ =
    ⟪u,referenceLowerAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i v⟫_ℝ
  simp only [referenceLowerCoordinateBoundaryFamily,referenceLowerAdjointCoordinateBoundaryFamily,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,inner_add_right]
  exact congrArg₂ (fun x y : ℝ => x+y) hTang hRad

variable (hg : IsAdmissibleMetric g)

theorem sphereSobolevDualPairing_referenceLowerJacobiBoundary_adjoint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,r))).IsInvertible)
    (u v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) v
      (referenceLowerJacobiBoundaryCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r i hInv u) =
    sphereSobolevDualPairing (1/2 : ℝ) u
      (referenceLowerAdjointJacobiBoundaryCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r i hInv v) := by
  have hTerm (j : Fin 3) :
      ⟪v,nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)
          (referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j u)⟫_ℝ =
      ⟪u,referenceLowerAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0
          (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv) v)⟫_ℝ := by
    have hM := ContinuousLinearMap.adjoint_inner_right
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)) v
      (referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j u)
    exact hM.trans (sphereSobolevDualPairing_referenceLowerCoordinateBoundary_adjoint
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j hWeak u
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0
          (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv) v))
  change ⟪v,referenceLowerJacobiBoundaryCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r i hInv u⟫_ℝ =
    ⟪u,referenceLowerAdjointJacobiBoundaryCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r i hInv v⟫_ℝ
  simp only [referenceLowerJacobiBoundaryCorrection,referenceLowerAdjointJacobiBoundaryCorrection,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,inner_sum]
  exact Finset.sum_congr rfl (fun j hj => hTerm j)

theorem sphereSobolevDualPairing_referenceLowerMovingBoundary_adjoint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible)
    (u v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) v
      (referenceLowerMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv u) =
    sphereSobolevDualPairing (1/2 : ℝ) u
      (referenceLowerAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv v) := by
  have hQ := sphereSobolevDualPairing_referenceLowerCoordinateBoundary_adjoint
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) i hWeak u v
  have hJ := sphereSobolevDualPairing_referenceLowerJacobiBoundary_adjoint
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y (R y) i hInv hWeak u v
  have hRad := sphereSobolevDualPairing_referenceLowerRadial_adjoint
    g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD (q,(y,R y)) hWeak u v
  have hCombined := congrArg₂ (fun a b : ℝ => a+b)
    (congrArg₂ (fun a b : ℝ => a+b)
      (congrArg (fun z : ℝ => (R y)⁻¹ * z) hQ)
      (congrArg (fun z : ℝ => R y * z) hJ))
    (congrArg (fun z : ℝ =>
      referenceRadiusHorizontalLogDerivative g L q R y i * z) hRad)
  simpa only [sphereSobolevDualPairing,referenceLowerMovingBoundaryAction,
    referenceLowerCenterBoundaryAction,referenceLowerAdjointMovingBoundaryAction,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    inner_add_right,real_inner_smul_right] using hCombined

theorem sphereLowerDistributionalTranspose_referenceLowerMovingBoundary
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    sphereLowerDistributionalTranspose
      (referenceLowerMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv) =
    referenceLowerAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro u
  change sphereSobolevDualPairing (1/2 : ℝ) u
      (sphereLowerDistributionalTranspose
        (referenceLowerMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv) v) =
    sphereSobolevDualPairing (1/2 : ℝ) u
      (referenceLowerAdjointMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv v)
  rw [← sphereSobolevDualPairing_lower_distributionalTranspose]
  exact sphereSobolevDualPairing_referenceLowerMovingBoundary_adjoint
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hInv hWeak u v

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_linearCoordinate_half_duality
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceLowerCoordinateBoundary_adjoint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceLowerJacobiBoundary_adjoint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceLowerMovingBoundary_adjoint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereLowerDistributionalTranspose_referenceLowerMovingBoundary
