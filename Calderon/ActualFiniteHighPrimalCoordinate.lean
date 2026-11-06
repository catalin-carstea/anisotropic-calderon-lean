import Calderon.ActualFiniteHarmonicHighRadialGraph
import Calderon.NativeFiniteHarmonicProductHighTangentialGraph
import Calderon.NativeThreeHalfUnitCoefficient
import Calderon.ActualHighMovingBoundaryAction

/-! The original uncompressed finite primal coordinate action; no PDE or image premise. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteHarmonicHighRadialFamily
  nativeFiniteHarmonicProductHighTangentialL referenceHighCoordinateBoundaryFamily
  sphereThreeHalfTangentialDerivativeL sphereSobolevLinearCoordinateMulL sphereSobolevInclusionL

def referenceFiniteHighPrimalCoordinateFamily (n : ℕ) (p : ℝ × (R3 × ℝ)) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  nativeFiniteHarmonicProductHighTangentialL hcalc hF hO hD τ0 n (unitSphereCoefficientJets 3) i +
  (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)).comp
    (referenceFiniteHarmonicHighRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n p)

lemma sphereSobolevInclusionL_referenceFiniteHighPrimalCoordinateFamily
    (hreg : FixedDirichletRegularity) (n : ℕ) (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a (p,z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w (p,z)‖ ≤ lam/4)
    (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceFiniteHighPrimalCoordinateFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n p i f) =
    referenceHighCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i
        (sphereSobolevPartialSum (3/2 : ℝ) n f) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let v := sphereSobolevPartialSum (3/2 : ℝ) n f
  let Rad := referenceFiniteHarmonicHighRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n p
  have hUnit : nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (unitSphereCoefficientJets 3) v = v :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) => A v)
      (nativeThreeHalfCoefficientMulL_unitSphereCoefficientJets hcalc hF hO hD τ0)
  have hTangential : I
      (nativeFiniteHarmonicProductHighTangentialL hcalc hF hO hD τ0 n
        (unitSphereCoefficientJets 3) i f) = sphereThreeHalfTangentialDerivativeL hF hO hD i v :=
    (sphereSobolevInclusionL_nativeFiniteHarmonicProductHighTangentialL hcalc hF hO hD τ0 n
      (unitSphereCoefficientJets 3) i f).trans
        (congrArg (sphereThreeHalfTangentialDerivativeL hF hO hD i) hUnit)
  have hRadial : I (Rad f) = referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p v :=
    sphereSobolevInclusionL_referenceFiniteHarmonicHighRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 n p lam Lam hUE hsmall f
  have hCoordinate :=
    (sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ)
      (by norm_num) (EuclideanSpace.single i 1) (Rad f)).trans
      (congrArg (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single i 1)) hRadial)
  have hSum := congrArg₂ (fun x y : SphereSobolev (1/2 : ℝ) => x+y) hTangential hCoordinate
  simpa only [referenceFiniteHighPrimalCoordinateFamily,referenceHighCoordinateBoundaryFamily,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,map_add,I,v,Rad] using hSum

lemma contDiffAt_referenceFiniteHighPrimalCoordinateFamily
    (n : ℕ) (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hi : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t => referenceFiniteHighPrimalCoordinateFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n t i) p := by
  have hRadial := contDiffAt_referenceFiniteHarmonicHighRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n p hi
  unfold referenceFiniteHighPrimalCoordinateFamily
  exact contDiffAt_const.add (contDiffAt_const.clm_comp hRadial)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFiniteHighPrimalCoordinateFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevInclusionL_referenceFiniteHighPrimalCoordinateFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFiniteHighPrimalCoordinateFamily
