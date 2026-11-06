import Calderon.ActualFiniteHighPrimalCoordinate
import Calderon.ActualHighMovingBoundaryFamily
import Calderon.ActualJacobiThreeHalfBoundaryMultiplierFamily
import Calderon.NativeOrderOneCoefficientMultiplier

/-! Full upfront: actual-primal-moving-adjoint-domain-author-oct16-v001/EXPANSION-v001.md.
Primal moving coefficients act on the LEFT, on the SAME original finite input. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteHighPrimalCoordinateFamily referenceFiniteHarmonicHighRadialFamily
  referenceHighMovingBoundaryActionFamily referenceHighCenterBoundaryActionFamily
  referenceHighJacobiBoundaryCorrectionFamily referenceRadiusHorizontalLogDerivative
  referenceJacobiBoundaryThreeHalfCoefficientFamily referenceJacobiBoundaryCoefficientFamily
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL sphereSobolevInclusionL

def referenceFiniteHighPrimalMovingBoundaryFamily
    (n : ℕ) (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  (R y)⁻¹ • referenceFiniteHighPrimalCoordinateFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n (q,(y,R y)) i +
  R y • (∑ j : Fin 3, (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceJacobiBoundaryThreeHalfCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData i j (q,(y,R y)))).comp
        (referenceFiniteHighPrimalCoordinateFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n (q,(y,R y)) j)) +
  referenceRadiusHorizontalLogDerivative g L q R y i • referenceFiniteHarmonicHighRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n (q,(y,R y))

lemma sphereSobolevInclusionL_referenceFiniteHighPrimalMovingBoundaryFamily
    (hreg : FixedDirichletRegularity) (n : ℕ) (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((q,(y,R y)),z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,R y)),z)‖ ≤ lam/4)
    (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceFiniteHighPrimalMovingBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R y i f) =
    referenceHighMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i
        (sphereSobolevPartialSum (3/2 : ℝ) n f) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let p := (q,(y,R y))
  let v := sphereSobolevPartialSum (3/2 : ℝ) n f
  let Cn := fun j : Fin 3 => referenceFiniteHighPrimalCoordinateFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n p j
  let C0 := referenceHighCoordinateBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let F3 := fun j : Fin 3 => referenceJacobiBoundaryThreeHalfCoefficientFamily
    g hg L y0 Φ B ε C ρ H a w hData i j p
  let F2 := fun j : Fin 3 => referenceJacobiBoundaryCoefficientFamily
    g hg L y0 Φ B ε C ρ H a w hData i j p
  have hCoordinate (j : Fin 3) : I (Cn j f) = C0 j v :=
    sphereSobolevInclusionL_referenceFiniteHighPrimalCoordinateFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg n p j lam Lam hUE hsmall f
  have hCoeff (j : Fin 3) : coefficientValue 3 (F3 j) = coefficientValue 2 (F2 j) := by
    simp only [F3,F2,referenceJacobiBoundaryThreeHalfCoefficientFamily,coefficientValue_compactCoefficient]
  have hJacobi (j : Fin 3) : I (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (F3 j) (Cn j f)) =
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 (F2 j) (C0 j v) :=
    (congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T (Cn j f))
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 (F3 j) (F2 j) (hCoeff j))).trans
        (congrArg (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (F2 j)) (hCoordinate j))
  have hJacobiSum : (∑ j : Fin 3, I (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (F3 j) (Cn j f))) =
      referenceHighJacobiBoundaryCorrectionFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p i v := by
    unfold referenceHighJacobiBoundaryCorrectionFamily
    simpa only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,C0,F2] using
      (Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => hJacobi j))
  have hRadial : I (referenceFiniteHarmonicHighRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n p f) =
      referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p v :=
    sphereSobolevInclusionL_referenceFiniteHarmonicHighRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 n p lam Lam hUE hsmall f
  have hCombined := congrArg₂ (fun z t : SphereSobolev (1/2 : ℝ) => z+t)
    (congrArg₂ (fun z t : SphereSobolev (1/2 : ℝ) => z+t)
      (congrArg (fun z : SphereSobolev (1/2 : ℝ) => (R y)⁻¹ • z) (hCoordinate i))
      (congrArg (fun z : SphereSobolev (1/2 : ℝ) => R y • z) hJacobiSum))
    (congrArg (fun z : SphereSobolev (1/2 : ℝ) => referenceRadiusHorizontalLogDerivative g L q R y i • z) hRadial)
  simpa only [referenceFiniteHighPrimalMovingBoundaryFamily,referenceHighMovingBoundaryActionFamily,
    referenceHighCenterBoundaryActionFamily,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_add,map_smul,map_sum,I,p,v,Cn,C0,F3]
    using hCombined

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFiniteHighPrimalMovingBoundaryFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevInclusionL_referenceFiniteHighPrimalMovingBoundaryFamily
