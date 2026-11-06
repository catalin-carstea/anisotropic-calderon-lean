import Calderon.ActualHighAdjointCoordinateActualJetTaylor

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

local instance : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceAdjointThreeHalfRadialFamily
  referenceRadialEndpointInvertibleLocus referenceHighAdjointCoordinateBoundaryFamily
  referenceHighAdjointJacobiBoundaryCorrection referenceHighAdjointMovingBoundaryAction
  referenceHighAdjointMovingBoundaryActionFamily
  nativeThreeHalfCoefficientMulL referenceJacobiBoundaryThreeHalfCoefficientJets
  sphereSobolevLinearCoordinateMulL sphereSobolevRotationL

lemma referenceHighAdjointMovingBoundaryActionFamily_actual_jet_decomposition
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hSegment : ∀ t ∈ uIcc (0 : ℝ) (R y), (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i =
      (R y)⁻¹ • referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) i +
      referenceRadiusHorizontalLogDerivative g L q R y i • referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) +
      referenceHighAdjointMovingActualJetFirstCorrection g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y)
        (referenceRadiusHorizontalLogDerivative g L q R y i) i +
      R y • referenceHighAdjointMovingActualJetNormalizedCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y (R y)
        (referenceRadiusHorizontalLogDerivative g L q R y i) i hInv := by
  have hMoving := referenceHighAdjointMovingBoundaryActionFamily_eq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i hInv
  refine hMoving.trans ?_
  have hRad := referenceAdjointThreeHalfRadialFamily_signed_actual_jet_taylor
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y (R y) hSegment
  have hCoord := referenceHighAdjointCoordinateBoundaryFamily_signed_actual_jet_taylor
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y (R y) i hSegment
  apply ContinuousLinearMap.ext
  intro u
  have hRadU := congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ]
    SphereSobolev (1/2 : ℝ) => A u) hRad
  have hCoordU := congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ]
    SphereSobolev (1/2 : ℝ) => A u) hCoord
  simp (config := { instances := true }) only
    [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply] at hRadU hCoordU
  have hSub := congrArg₂ (fun c z : SphereSobolev (1/2 : ℝ) =>
    (R y)⁻¹ • c + R y •
      (referenceHighAdjointJacobiBoundaryCorrection g L y0 Φ B ε C ρ H a w hData
        hg hcalc hF hO hD τ0 q y (R y) i hInv u) +
      referenceRadiusHorizontalLogDerivative g L q R y i • z) hCoordU hRadU
  have hAlg (r f : ℝ) (hr0 : r ≠ 0) (C0 DMi SMi J Z0 Du Su : SphereSobolev (1/2 : ℝ)) :
      r⁻¹ • (C0+r • DMi+r^2 • SMi)+r • J+f • (Z0+r • Du+r^2 • Su) =
        r⁻¹ • C0+f • Z0+(DMi+(r*f) • Du)+r • (SMi+J+(r*f) • Su) := by
    have h1 : r⁻¹*r = 1 := inv_mul_cancel₀ hr0
    have h2 : r⁻¹*r^2 = r := by field_simp [hr0] <;> ring
    simp only [smul_add,smul_smul,h1,h2,one_smul]
    module
  have hEnd := hSub.trans
    (hAlg (R y) (referenceRadiusHorizontalLogDerivative g L q R y i) hr _ _ _ _ _ _ _)
  simpa (config := { instances := true }) only
    [referenceHighAdjointMovingBoundaryAction,
      referenceHighAdjointMovingActualJetFirstCorrection,
      referenceHighAdjointMovingActualJetNormalizedCorrection,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply] using hEnd


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingBoundaryActionFamily_actual_jet_decomposition
