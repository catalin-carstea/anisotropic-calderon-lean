import Calderon.NativeCoordinateTraceVariation
import Calderon.ActualBoundedNativeRadialCorrection

/-! Bounded actual coordinate first correction: the completed-space operator bound
and the actual native constant/positive core derivative identities. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory MvPolynomial
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

def coordinateRadialDriftTraceL (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) (i : Fin 3) : SphereL2 →L[ℝ] SphereL2 :=
  (sphereCoordinateMulL i).comp (radialDriftTraceL hF hO hD d)

theorem norm_coordinateRadialDriftTraceL_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) (i : Fin 3) :
    ‖coordinateRadialDriftTraceL hF hO hD d i‖ ≤ 2 * ∑ j : Fin 3, |d j| := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (norm_sphereCoordinateMulL_le i) (norm_radialDriftTraceL_le hF hO hD d)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))

theorem coordinateRadialDriftTraceL_constant (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) (i : Fin 3) (a : harmonicSphereSubspace 0) :
    coordinateRadialDriftTraceL hF hO hD d i (a : SphereL2) = 0 := by
  rw [coordinateRadialDriftTraceL,ContinuousLinearMap.comp_apply,
    radialDriftTraceL_constant,map_zero]

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem hasDerivAt_referenceCoordinateHarmonicLiftFamily_bounded_firstCorrection
    (hzero : SmoothBoundaryZeroClosure) (hcalc : FixedSobolevCalculus)
    (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (m : ℕ) (p : harmonicHomogeneous (m+1)) (i : Fin 3) :
    HasDerivAt
      (fun r : ℝ => strongCoordinateTraceL hcalc τ0 i
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r)
          (polynomialBallSobolev 2 p)))
      (coordinateRadialDriftTraceL hF hO hD (referenceCenterDrift g L q y) i (polynomialSphereL2 p)) 0 := by
  have hP := hasDerivAt_referenceHarmonicLiftFamily_driftFirstVariation_zero
    g L y0 Φ B ε C ρ H a w hData hzero hcalc hreg 0 q hq y hy (m+1) p p.property.1 p.property.2
  have hτ := (strongCoordinateTraceL hcalc τ0 i).hasFDerivAt.comp_hasDerivAt 0 hP
  simp only [Function.comp_def] at hτ
  rw [strongCoordinateTraceL_driftFirstVariation,
    outwardRadialTraceL_driftFirstVariation hcalc τ0 (by omega),
    ← radialDriftTraceL_polynomial hF hO hD (referenceCenterDrift g L q y) m p] at hτ
  exact hτ

theorem hasDerivAt_referenceCoordinateHarmonicLiftFamily_constant_firstCorrection
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (p : harmonicHomogeneous 0) (i : Fin 3) :
    HasDerivAt
      (fun r : ℝ => strongCoordinateTraceL hcalc τ0 i
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r)
          (polynomialBallSobolev 2 p)))
      (coordinateRadialDriftTraceL hF hO hD (referenceCenterDrift g L q y) i (polynomialSphereL2 p)) 0 := by
  have hdp : GreenRadialTrace.driftDerivative
      (polynomialCoordinateMap (referenceCenterDrift g L q y)) p = 0 := by
    simp only [GreenRadialTrace.driftDerivative,
      CurvatureContraction.pderiv_eq_zero_of_isHomogeneous_zero p p.property.1,
      mul_zero,Finset.sum_const_zero]
  have hP := hasDerivAt_referenceHarmonicLiftFamily_polynomial_zero
    g L y0 Φ B ε C ρ H a w hData hcalc hreg 0 q hq y hy p p.property.2
  have hτ := (strongCoordinateTraceL hcalc τ0 i).hasFDerivAt.comp_hasDerivAt 0 hP
  have hG : coordinateRadialDriftTraceL hF hO hD (referenceCenterDrift g L q y) i
      (polynomialSphereL2 p) = 0 :=
    coordinateRadialDriftTraceL_constant hF hO hD (referenceCenterDrift g L q y) i
      ⟨polynomialSphereL2 p,polynomialSphereL2_mem 0 p p.property⟩
  rw [hG]
  have h0 : polynomialBallSobolev 0 (0 : MvPolynomial (Fin 3) ℝ) = 0 := by
    change polynomialBallSobolevLinearMap 0 0 = 0
    exact map_zero _
  simpa only [Function.comp_def,hdp,h0,map_zero] using hτ

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
