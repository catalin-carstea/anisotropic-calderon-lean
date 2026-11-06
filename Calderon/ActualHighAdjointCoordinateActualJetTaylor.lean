import Calderon.ActualHighAdjointMovingTraceActualJetData

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

lemma referenceHighAdjointCoordinateBoundaryFamily_signed_actual_jet_taylor
    (hreg : FixedDirichletRegularity) (q : ℝ) (y : R3) (r : ℝ) (i : Fin 3)
    (hSegment : ∀ t ∈ uIcc (0 : ℝ) r, (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) i =
      referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) i +
      r • (deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0).comp (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)) +
      r^2 • (referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r).comp
        (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)) := by
  have hTaylor := referenceAdjointThreeHalfRadialFamily_signed_actual_jet_taylor
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment
  apply ContinuousLinearMap.ext
  intro u
  have ht := congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ]
      SphereSobolev (1/2 : ℝ) => A
        (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1) u)) hTaylor
  simp (config := { instances := true }) only
    [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply] at ht
  let P : SphereSobolev (1/2 : ℝ) :=
    -(∑ j : Fin 3, (sphereSobolevRotationL (3/2 : ℝ) j i).comp
      (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
        (EuclideanSpace.single j 1))) u
  have hShift := congrArg (fun v : SphereSobolev (1/2 : ℝ) => P + v) ht
  simpa (config := { instances := true }) only
    [referenceHighAdjointCoordinateBoundaryFamily,P,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,add_assoc]
    using hShift


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointCoordinateBoundaryFamily_signed_actual_jet_taylor
