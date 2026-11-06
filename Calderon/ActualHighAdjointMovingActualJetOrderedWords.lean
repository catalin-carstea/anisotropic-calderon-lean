import Calderon.ActualHighAdjointCoordinateActualJetTaylor

/-! Full upfront: raw-moving-adjoint-split-author-oct16-v001/EXPANSION.md.
Exact unchanged selected declarations from compiled-only a974 Raw7. -/
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

lemma referenceHighAdjointMovingActualJetNormalizedCorrection_eq_ordered_words
    (hreg : FixedDirichletRegularity) (q : ℝ) (y : R3) (r f : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) (hSegment : ∀ t ∈ uIcc (0 : ℝ) r, (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceHighAdjointMovingActualJetNormalizedCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r f i hInv =
      (referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r).comp (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)) +
      (∑ j : Fin 3, (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j).comp
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (referenceJacobiBoundaryThreeHalfCoefficientJets g L y0 Φ B ε C ρ H a w hData hg q y r i j hInv))) +
      r • (∑ j : Fin 3, (deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0).comp
        ((sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)).comp
          (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (referenceJacobiBoundaryThreeHalfCoefficientJets g L y0 Φ B ε C ρ H a w hData hg q y r i j hInv)))) +
      r^2 • (∑ j : Fin 3, (referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r).comp
        ((sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)).comp
          (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (referenceJacobiBoundaryThreeHalfCoefficientJets g L y0 Φ B ε C ρ H a w hData hg q y r i j hInv)))) +
      (r*f) • referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r := by
  apply ContinuousLinearMap.ext
  intro u
  let Nj := fun j : Fin 3 => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (referenceJacobiBoundaryThreeHalfCoefficientJets g L y0 Φ B ε C ρ H a w hData hg q y r i j hInv)
  have hJac : referenceHighAdjointJacobiBoundaryCorrection g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r i hInv u =
      (∑ j : Fin 3, referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j (Nj j u)) +
      r • (∑ j : Fin 3, (deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0)
        (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1) (Nj j u))) +
      r^2 • (∑ j : Fin 3, referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
        (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1) (Nj j u))) := by
    simp only [referenceHighAdjointJacobiBoundaryCorrection,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
    change (∑ j : Fin 3, referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) j (Nj j u)) = _
    calc
      _ = ∑ j : Fin 3, (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j (Nj j u) +
          r • (deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0) (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1) (Nj j u)) +
          r^2 • referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
            (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1) (Nj j u))) := by
        apply Finset.sum_congr rfl
        intro j hj
        have h := congrArg (fun Cj : SphereSobolev (3/2 : ℝ) →L[ℝ]
            SphereSobolev (1/2 : ℝ) => Cj (Nj j u))
          (referenceHighAdjointCoordinateBoundaryFamily_signed_actual_jet_taylor
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r j hSegment)
        simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.comp_apply] using h
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.smul_sum]
  have hCombined := congrArg (fun v : SphereSobolev (1/2 : ℝ) =>
    referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 q y r
        (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
          (EuclideanSpace.single i 1) u) + v +
      (r*f) • referenceHighAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w
        hData hcalc hF hO hD τ0 q y r u) hJac
  simpa (config := { instances := true }) only
    [referenceHighAdjointMovingActualJetNormalizedCorrection,Nj,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,add_assoc]
    using hCombined

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingActualJetNormalizedCorrection_eq_ordered_words
