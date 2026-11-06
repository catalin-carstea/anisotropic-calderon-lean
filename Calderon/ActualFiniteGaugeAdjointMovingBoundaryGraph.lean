import Calderon.ActualFiniteGaugeAdjointUnitCoordinateGraph
import Calderon.ActualFiniteGaugeAdjointJacobiCoordinateGraph
import Calderon.ActualFiniteGaugeAdjointUnitRadialGraph
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

lemma sphereSobolevInclusionL_referenceFiniteGaugeAdjointMovingBoundaryFamily_of_coefficient_eq
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (n : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a ((q,(y,R y)),z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,R y)),z)‖ ≤ lam/4)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hG : (q,(y,R y)) ∈ G.parameterRoom) (i : Fin 3)
    (hCoeff : ∀ j : Fin 3, nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (E.jets i j (q,(y,R y))) =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j (q,(y,R y))))
    (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceFiniteGaugeAdjointMovingBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R y i f) =
    referenceHighAdjointMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i
        (sphereSobolevPartialSum (3/2 : ℝ) n f) := by
  let p := (q,(y,R y))
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let v := sphereSobolevPartialSum (3/2 : ℝ) n f
  let D := referenceHighAdjointCoordinateBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Z := referenceAdjointThreeHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  have hCoordinate : I (referenceFiniteGaugeAdjointCoordinateFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (unitSphereCoefficientJets 3) p i f) = D i v :=
    sphereSobolevInclusionL_referenceFiniteGaugeAdjointCoordinateFamily_unit
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G
        hreg hKernel n q hq y hy (R y) lam Lam hUE hsmall hp hG i f
  have hJacobiSum : (∑ j : Fin 3, I (referenceFiniteGaugeAdjointCoordinateFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (E.jets i j p) p j f)) =
      referenceHighAdjointJacobiBoundaryCorrectionFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p i v :=
    sphereSobolevInclusionL_referenceFiniteGaugeAdjointCoordinateFamily_jacobiSum
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E
        hreg hKernel n q hq y hy (R y) lam Lam hUE hsmall hp hG i hCoeff f
  have hRadial : I (referenceFiniteGaugeAdjointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (unitSphereCoefficientJets 3) p f) = Z v :=
    sphereSobolevInclusionL_referenceFiniteGaugeAdjointRadialFamily_unit
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G
        hreg hKernel n q hq y hy (R y) lam Lam hUE hsmall hp hG f
  have hCombined := congrArg₂ (fun z t : SphereSobolev (1/2 : ℝ) => z+t)
    (congrArg₂ (fun z t : SphereSobolev (1/2 : ℝ) => z+t)
      (congrArg (fun z : SphereSobolev (1/2 : ℝ) => (R y)⁻¹ • z) hCoordinate)
      (congrArg (fun z : SphereSobolev (1/2 : ℝ) => R y • z) hJacobiSum))
    (congrArg (fun z : SphereSobolev (1/2 : ℝ) => referenceRadiusHorizontalLogDerivative g L q R y i • z) hRadial)
  simpa only [referenceFiniteGaugeAdjointMovingBoundaryFamily,referenceHighAdjointMovingBoundaryActionFamily,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    map_add,map_smul,map_sum,I,p,v,D,Z] using hCombined

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevInclusionL_referenceFiniteGaugeAdjointMovingBoundaryFamily_of_coefficient_eq
