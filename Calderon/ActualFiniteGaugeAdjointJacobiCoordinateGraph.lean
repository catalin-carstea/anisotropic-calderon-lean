import Calderon.ActualFiniteGaugeAdjointMovingBoundaryFamily
import Calderon.ActualFiniteGaugeAdjointCoordinateGraph

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
DIRECT-MOVING-GRAPH-PROOF-DECOMPOSITION-UPFRONT-v001.md. Exact original moving graph proof block. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteGaugeAdjointMovingBoundaryFamily
  referenceHighAdjointCoordinateBoundaryFamily referenceFiniteGaugeAdjointCoordinateFamily
  referenceFiniteGaugeAdjointRadialFamily referenceHighAdjointMovingBoundaryActionFamily
  referenceHighAdjointJacobiBoundaryCorrectionFamily nativeThreeHalfCoefficientMulL
  sphereSobolevInclusionL referenceStrongDriftFamily
  referenceRadiusHorizontalLogDerivative

variable {KG KJ : Set (ℝ × (R3 × ℝ))}
  (G : ReferenceGaugeNormalReciprocalRoom g L Φ a KG)
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) KJ)

lemma sphereSobolevInclusionL_referenceFiniteGaugeAdjointCoordinateFamily_jacobiSum
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (n : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r : ℝ) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a ((q,(y,r)),z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z)‖ ≤ lam/4)
    (hp : (q,(y,r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hG : (q,(y,r)) ∈ G.parameterRoom) (i : Fin 3)
    (hCoeff : ∀ j : Fin 3, nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (E.jets i j (q,(y,r))) =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j (q,(y,r))))
    (f : SphereSobolev (3/2 : ℝ)) :
    (∑ j : Fin 3, sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceFiniteGaugeAdjointCoordinateFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n
          (E.jets i j (q,(y,r))) (q,(y,r)) j f)) =
    referenceHighAdjointJacobiBoundaryCorrectionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r)) i
        (sphereSobolevPartialSum (3/2 : ℝ) n f) := by
  let p := (q,(y,r))
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let v := sphereSobolevPartialSum (3/2 : ℝ) n f
  let D := referenceHighAdjointCoordinateBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  have hCoeffPoint (j : Fin 3) :
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (E.jets i j p) v =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j p) v :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) => A v) (hCoeff j)
  have hJacobi (j : Fin 3) : I (referenceFiniteGaugeAdjointCoordinateFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (E.jets i j p) p j f) =
      D j (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j p) v) :=
    (sphereSobolevInclusionL_referenceFiniteGaugeAdjointCoordinateFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel G n
        (E.jets i j p) q hq y hy r lam Lam hUE hsmall hp hG j f).trans
      (congrArg (fun z : SphereSobolev (3/2 : ℝ) => D j z) (hCoeffPoint j))
  unfold referenceHighAdjointJacobiBoundaryCorrectionFamily
  simpa only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply] using
    (Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => hJacobi j))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevInclusionL_referenceFiniteGaugeAdjointCoordinateFamily_jacobiSum
