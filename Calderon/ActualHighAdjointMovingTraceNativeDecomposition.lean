import Calderon.ActualHighAdjointMovingTraceActualJets
import Calderon.ActualReferenceHighAdjointRadialNativeJets

/-! The actual moving family, with the native B and first jet derived; no graph
premise. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.SphereHarmonic

def sphereHighHarmonicDerivativeTransposeL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i : Fin 3) : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  -(∑ j : Fin 3, (sphereSobolevRotationL (3/2 : ℝ) j i).comp
      (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1))) +
    (sphereSobolevShiftedDegreeL (3/2 : ℝ)).comp
      (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1))

end OAI.AnisotropicCalderon.SphereHarmonic
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

def referenceHighAdjointMovingFirstCorrection
    (g : MatrixField) (L : ℝ) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (q : ℝ) (y : R3) (r f : ℝ) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  (sphereSobolevRadialDriftAdjointL hF hO hD (3/2 : ℝ) (referenceCenterDrift g L q y)).comp (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)) +
    (r*f) • sphereSobolevRadialDriftAdjointL hF hO hD (3/2 : ℝ) (referenceCenterDrift g L q y)

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

lemma referenceHighAdjointCoordinateBoundaryFamily_zero_eq_harmonicDerivativeTranspose
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (i : Fin 3) :
    referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) i = sphereHighHarmonicDerivativeTransposeL hF hO hD i := by
  unfold referenceHighAdjointCoordinateBoundaryFamily sphereHighHarmonicDerivativeTransposeL
  rw [referenceAdjointThreeHalfRadialFamily_zero_eq_shiftedDegree g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy]

attribute [local irreducible] referenceAdjointThreeHalfRadialFamily
  referenceRadialEndpointInvertibleLocus referenceHighAdjointCoordinateBoundaryFamily
  referenceHighAdjointMovingBoundaryActionFamily
  referenceHighAdjointRadialSecondRemainder
  referenceHighAdjointMovingActualJetNormalizedCorrection
  nativeThreeHalfCoefficientMulL referenceJacobiBoundaryThreeHalfCoefficientJets
  sphereSobolevLinearCoordinateMulL sphereSobolevRotationL
  sphereSobolevRadialDriftAdjointL sphereSobolevInclusionL sphereSobolevShiftedDegreeL

lemma referenceHighAdjointMovingActualJetFirstCorrection_eq_native
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r f : ℝ) (i : Fin 3) :
    referenceHighAdjointMovingActualJetFirstCorrection g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r f i =
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp (referenceHighAdjointMovingFirstCorrection g L hF hO hD q y r f i) := by
  have hDjet := deriv_referenceAdjointThreeHalfRadialFamily_zero_eq_nativeFirstCorrection
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  apply ContinuousLinearMap.ext
  intro u
  have h1 := congrArg (fun D : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
    D (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1) u)) hDjet
  have h2 := congrArg (fun D : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => D u) hDjet
  simp (config := { instances := true }) only [ContinuousLinearMap.comp_apply] at h1 h2
  have hValue := congrArg₂ (fun x z : SphereSobolev (1/2 : ℝ) =>
    x + (r*f) • z) h1 h2
  simpa (config := { instances := true }) only
    [referenceHighAdjointMovingActualJetFirstCorrection,
      referenceHighAdjointMovingFirstCorrection,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,map_add,map_smul]
    using hValue

lemma referenceAdjointThreeHalfRadialFamily_signed_native_taylor
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r : ℝ) (hSegment : ∀ t ∈ uIcc (0 : ℝ) r, (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) = sphereSobolevShiftedDegreeL (3/2 : ℝ) +
      r • (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp (sphereSobolevRadialDriftAdjointL hF hO hD (3/2 : ℝ) (referenceCenterDrift g L q y)) + r^2 • referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r := by
  have h := referenceAdjointThreeHalfRadialFamily_signed_actual_jet_taylor
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment
  have hZero := referenceAdjointThreeHalfRadialFamily_zero_eq_shiftedDegree
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hFirst := deriv_referenceAdjointThreeHalfRadialFamily_zero_eq_nativeFirstCorrection
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  apply ContinuousLinearMap.ext
  intro u
  have hRawU := congrArg (fun D : SphereSobolev (3/2 : ℝ) →L[ℝ]
    SphereSobolev (1/2 : ℝ) => D u) h
  have hZeroU := congrArg (fun D : SphereSobolev (3/2 : ℝ) →L[ℝ]
    SphereSobolev (1/2 : ℝ) => D u) hZero
  have hFirstU := congrArg (fun D : SphereSobolev (3/2 : ℝ) →L[ℝ]
    SphereSobolev (1/2 : ℝ) => D u) hFirst
  let tail : SphereSobolev (1/2 : ℝ) := r^2 •
    referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 q y r u
  have hChange := congrArg₂ (fun x z : SphereSobolev (1/2 : ℝ) =>
    x + r • z + tail) hZeroU hFirstU
  simp (config := { instances := true }) only
    [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply] at hRawU
  simpa (config := { instances := true }) only
    [tail,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply]
    using hRawU.trans hChange

lemma referenceHighAdjointMovingBoundaryActionFamily_native_decomposition
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (R : R3 → ℝ) (i : Fin 3) (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hSegment : ∀ t ∈ uIcc (0 : ℝ) (R y), (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i =
      (R y)⁻¹ • sphereHighHarmonicDerivativeTransposeL hF hO hD i +
      referenceRadiusHorizontalLogDerivative g L q R y i • sphereSobolevShiftedDegreeL (3/2 : ℝ) +
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp (referenceHighAdjointMovingFirstCorrection g L hF hO hD q y (R y)
        (referenceRadiusHorizontalLogDerivative g L q R y i) i) +
      R y • referenceHighAdjointMovingActualJetNormalizedCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y (R y)
        (referenceRadiusHorizontalLogDerivative g L q R y i) i hInv := by
  have h := referenceHighAdjointMovingBoundaryActionFamily_actual_jet_decomposition
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R y i hr hInv hSegment
  have hCoord := referenceHighAdjointCoordinateBoundaryFamily_zero_eq_harmonicDerivativeTranspose
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i
  have hZero := referenceAdjointThreeHalfRadialFamily_zero_eq_shiftedDegree
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hFirst := referenceHighAdjointMovingActualJetFirstCorrection_eq_native
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy (R y)
      (referenceRadiusHorizontalLogDerivative g L q R y i) i
  apply ContinuousLinearMap.ext
  intro u
  have hRawU := congrArg (fun D : SphereSobolev (3/2 : ℝ) →L[ℝ]
    SphereSobolev (1/2 : ℝ) => D u) h
  have hCoordU := congrArg (fun D : SphereSobolev (3/2 : ℝ) →L[ℝ]
    SphereSobolev (1/2 : ℝ) => D u) hCoord
  have hZeroU := congrArg (fun D : SphereSobolev (3/2 : ℝ) →L[ℝ]
    SphereSobolev (1/2 : ℝ) => D u) hZero
  have hFirstU := congrArg (fun D : SphereSobolev (3/2 : ℝ) →L[ℝ]
    SphereSobolev (1/2 : ℝ) => D u) hFirst
  have hHead := congrArg₂ (fun x z : SphereSobolev (1/2 : ℝ) =>
    (R y)⁻¹ • x + referenceRadiusHorizontalLogDerivative g L q R y i • z)
      hCoordU hZeroU
  let tail : SphereSobolev (1/2 : ℝ) := R y •
    referenceHighAdjointMovingActualJetNormalizedCorrection g L y0 Φ B ε C ρ H a w
      hData hg hcalc hF hO hD τ0 q y (R y)
      (referenceRadiusHorizontalLogDerivative g L q R y i) i hInv u
  have hChange := congrArg₂ (fun head first : SphereSobolev (1/2 : ℝ) =>
    head + first + tail) hHead hFirstU
  simp (config := { instances := true }) only
    [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply] at hRawU
  simpa (config := { instances := true }) only
    [tail,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply]
    using hRawU.trans hChange

lemma referenceHighAdjointMovingActualJetNormalizedCorrection_eq_native_ordered_words
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r f : ℝ) (i : Fin 3) (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) (hSegment : ∀ t ∈ uIcc (0 : ℝ) r, (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceHighAdjointMovingActualJetNormalizedCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r f i hInv =
      (referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r).comp (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)) +
      (∑ j : Fin 3, (sphereHighHarmonicDerivativeTransposeL hF hO hD j).comp
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (referenceJacobiBoundaryThreeHalfCoefficientJets g L y0 Φ B ε C ρ H a w hData hg q y r i j hInv))) +
      r • (∑ j : Fin 3, ((sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp (sphereSobolevRadialDriftAdjointL hF hO hD (3/2 : ℝ) (referenceCenterDrift g L q y))).comp
        ((sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)).comp
          (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (referenceJacobiBoundaryThreeHalfCoefficientJets g L y0 Φ B ε C ρ H a w hData hg q y r i j hInv)))) +
      r^2 • (∑ j : Fin 3, (referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r).comp
        ((sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)).comp
          (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (referenceJacobiBoundaryThreeHalfCoefficientJets g L y0 Φ B ε C ρ H a w hData hg q y r i j hInv)))) +
      (r*f) • referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r := by
  let Nj := fun j : Fin 3 => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (referenceJacobiBoundaryThreeHalfCoefficientJets g L y0 Φ B ε C ρ H a w hData hg q y r i j hInv)
  have hDjet := deriv_referenceAdjointThreeHalfRadialFamily_zero_eq_nativeFirstCorrection
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hCoord : (∑ j : Fin 3, (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j).comp (Nj j)) =
      ∑ j : Fin 3, (sphereHighHarmonicDerivativeTransposeL hF hO hD j).comp (Nj j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun Cj : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      Cj.comp (Nj j)) (referenceHighAdjointCoordinateBoundaryFamily_zero_eq_harmonicDerivativeTranspose
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy j)
  have hDsum : (∑ j : Fin 3, (deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0).comp
        ((sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)).comp (Nj j))) =
      ∑ j : Fin 3, ((sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp (sphereSobolevRadialDriftAdjointL hF hO hD (3/2 : ℝ) (referenceCenterDrift g L q y))).comp
        ((sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)).comp (Nj j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun D : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      D.comp ((sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)).comp (Nj j))) hDjet
  have hRaw := referenceHighAdjointMovingActualJetNormalizedCorrection_eq_ordered_words
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q y r f i hInv hSegment
  apply ContinuousLinearMap.ext
  intro u
  have hRawU := congrArg (fun D : SphereSobolev (3/2 : ℝ) →L[ℝ]
    SphereSobolev (1/2 : ℝ) => D u) hRaw
  have hCoordU := congrArg (fun D : SphereSobolev (3/2 : ℝ) →L[ℝ]
    SphereSobolev (1/2 : ℝ) => D u) hCoord
  have hDsumU := congrArg (fun D : SphereSobolev (3/2 : ℝ) →L[ℝ]
    SphereSobolev (1/2 : ℝ) => D u) hDsum
  let tail0 : SphereSobolev (1/2 : ℝ) :=
    (referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 q y r).comp
      (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
        (EuclideanSpace.single i 1)) u
  let tail2 : SphereSobolev (1/2 : ℝ) := r^2 •
    (∑ j : Fin 3, (referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 q y r).comp
        ((sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
          (EuclideanSpace.single j 1)).comp (Nj j))) u
  let tailF : SphereSobolev (1/2 : ℝ) := (r*f) •
    referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 q y r u
  have hChange := congrArg₂ (fun c d : SphereSobolev (1/2 : ℝ) =>
    tail0 + c + r • d + tail2 + tailF) hCoordU hDsumU
  simp (config := { instances := true }) only
    [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply] at hRawU
  simpa (config := { instances := true }) only
    [tail0,tail2,tailF,Nj,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply]
    using hRawU.trans hChange

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereHighHarmonicDerivativeTransposeL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingFirstCorrection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointCoordinateBoundaryFamily_zero_eq_harmonicDerivativeTranspose
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingActualJetFirstCorrection_eq_native
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointThreeHalfRadialFamily_signed_native_taylor
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingBoundaryActionFamily_native_decomposition
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingActualJetNormalizedCorrection_eq_native_ordered_words
