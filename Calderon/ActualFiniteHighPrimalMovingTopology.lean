import Calderon.ActualFiniteHighPrimalMoving

/-! Primal moving coefficients act on the left, on the same finite input. -/
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

lemma contDiffAt_referenceFiniteHighPrimalMovingBoundaryFamily
    (n : ℕ) (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hi : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,R y)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun x => referenceFiniteHighPrimalMovingBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R x i) y := by
  letI : IsBoundedSMul ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    IsBoundedSMul.of_norm_smul_le (fun c T => ContinuousLinearMap.opNorm_smul_le c T)
  let p := (q,(y,R y))
  let P : R3 → ℝ × (R3 × ℝ) := fun x => (q,(x,R x))
  have hP : ContDiffAt ℝ ∞ P y := contDiffAt_const.prodMk (contDiffAt_id.prodMk hR)
  have hCoordinate (j : Fin 3) : ContDiffAt ℝ ∞ (fun x => referenceFiniteHighPrimalCoordinateFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n (P x) j) y := by
    have hJoint : ContDiffAt ℝ ∞ (fun t : ℝ × (R3 × ℝ) =>
        referenceFiniteHighPrimalCoordinateFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n t j) (P y) :=
      contDiffAt_referenceFiniteHighPrimalCoordinateFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n (P y) j hi
    have hComposed := hJoint.comp (f := P) y hP
    simpa only [Function.comp_def] using hComposed
  have hRadial : ContDiffAt ℝ ∞ (fun x => referenceFiniteHarmonicHighRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n (P x)) y :=
    (contDiffAt_referenceFiniteHarmonicHighRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n p hi).comp y hP
  have hJacobi : ContDiffAt ℝ ∞ (fun x => ∑ j : Fin 3,
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryThreeHalfCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j (P x))).comp
            (referenceFiniteHighPrimalCoordinateFamily
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n (P x) j)) y := by
    apply ContDiffAt.sum
    intro j hj
    exact ((contDiffAt_nativeThreeHalf_referenceJacobiBoundaryThreeHalfCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hInv).comp y hP).clm_comp
        (hCoordinate j)
  have hScalar : ContDiffAt ℝ ∞ (fun x => referenceRadiusHorizontalLogDerivative g L q R x i) y :=
    (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R (q,y) i hR hr).comp y
      (contDiffAt_const.prodMk contDiffAt_id)
  simpa (config := { instances := true }) only
    [referenceFiniteHighPrimalMovingBoundaryFamily,P,Pi.smul_def',Pi.add_def,Pi.inv_apply] using
    (((hR.inv hr).smul (hCoordinate i)).add (hR.smul hJacobi)).add (hScalar.smul hRadial)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFiniteHighPrimalMovingBoundaryFamily
