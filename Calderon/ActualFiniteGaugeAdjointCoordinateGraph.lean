import Calderon.ActualFiniteGaugeAdjointCoordinateFamily
import Calderon.ActualFiniteGaugeAdjointRadialGraph
import Calderon.ActualAdjointMovingBoundaryAction

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
FINITE-GAUGE-ADJOINT-COORDINATE-MOVING-DOMAIN-EXPANSION-v001.md. Actual derivative AFTER coordinate product. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier NativeHarmonicLiftCompletion

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] nativeThreeHalfCoefficientMulL nativeFiniteHarmonicProductHighRotationL
  referenceFiniteGaugeAdjointRadialFamily sphereSobolevInclusionL
  sphereSobolevLinearCoordinateMulL sphereSobolevRotationL referenceHighAdjointCoordinateBoundaryFamily

variable {K0 : Set (ℝ × (R3 × ℝ))}

lemma sphereSobolevInclusionL_referenceFiniteGaugeAdjointCoordinateFamily
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K0) (n : ℕ)
    (Q : SmoothCoefficientJets 3) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a ((q,(y,r)),z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z)‖ ≤ lam/4)
    (hp : (q,(y,r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hG : (q,(y,r)) ∈ G.parameterRoom) (i : Fin 3) (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceFiniteGaugeAdjointCoordinateFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n Q (q,(y,r)) i f) =
    referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) i
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
          (sphereSobolevPartialSum (3/2 : ℝ) n f)) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let x := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
    (sphereSobolevPartialSum (3/2 : ℝ) n f)
  let X : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun j =>
    sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)
  have hProduct (j : Fin 3) :
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (coefficientCoordinateJets Q j)
        (sphereSobolevPartialSum (3/2 : ℝ) n f) = X j x :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) =>
      A (sphereSobolevPartialSum (3/2 : ℝ) n f))
      (nativeThreeHalfCoefficientMulL_coordinateJets hcalc hF hO hD τ0 Q j)
  have hRotation (j : Fin 3) :
      I (nativeFiniteHarmonicProductHighRotationL hcalc hF hO hD τ0 n
        (coefficientCoordinateJets Q j) j i f) = sphereSobolevRotationL (3/2 : ℝ) j i (X j x) :=
    (sphereSobolevInclusionL_nativeFiniteHarmonicProductHighRotationL
      hcalc hF hO hD τ0 n (coefficientCoordinateJets Q j) j i f).trans
      (congrArg (sphereSobolevRotationL (3/2 : ℝ) j i) (hProduct j))
  have hRadial : I (referenceFiniteGaugeAdjointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (coefficientCoordinateJets Q i) (q,(y,r)) f) =
      referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) (X i x) :=
    (sphereSobolevInclusionL_referenceFiniteGaugeAdjointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel G n
        (coefficientCoordinateJets Q i) q hq y hy r lam Lam hUE hsmall hp hG f).trans
      (congrArg (referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))) (hProduct i))
  have hSum : (∑ j : Fin 3, I (nativeFiniteHarmonicProductHighRotationL
      hcalc hF hO hD τ0 n (coefficientCoordinateJets Q j) j i f)) =
      ∑ j : Fin 3, sphereSobolevRotationL (3/2 : ℝ) j i (X j x) :=
    Finset.sum_congr rfl (fun j _ => hRotation j)
  simp only [referenceFiniteGaugeAdjointCoordinateFamily,referenceHighAdjointCoordinateBoundaryFamily,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,map_add,map_neg,map_sum]
  exact congrArg₂ (fun z t : SphereSobolev (1/2 : ℝ) => -z+t) hSum hRadial

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevInclusionL_referenceFiniteGaugeAdjointCoordinateFamily
