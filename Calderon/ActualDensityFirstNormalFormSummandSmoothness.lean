import Calderon.ActualWeightedHorizontalActions
import Calderon.ActualNativeMovingHighLocalRemainderSmoothness

/-! Before-source: actual-physical-full-allocation-author-oct16-v001/
EXPANSION-normal-form-summands-smoothness-v007.md. Actual summands on the same input. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighWeightedHorizontalAction
  referenceNativeMovingAdjointParametricCorrection referenceHighAdjointMovingDifferenceQuotient
  sphereSobolevAngularCoordinateTransposeL sphereSobolevInclusionL
  referenceRadialEndpointInvertibleLocus

lemma contDiffAt_referenceHighDensityFirstAction_normal_form_summands
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0) (hu : ContDiffAt ℝ ∞ u y)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun x => referenceHighWeightedHorizontalAction g L q R u x i) y ∧
    ContDiffAt ℝ ∞ (fun x => (R x)⁻¹ •
      sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i (u x)) y ∧
    ContDiffAt ℝ ∞ (fun x => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
        ((q,x),fderiv ℝ R x) i (u x))) y ∧
    ContDiffAt ℝ ∞ (fun x => R x • referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x i (u x)) y := by
  have hWeighted := contDiffAt_referenceHighWeightedHorizontalAction g hg L q R u y i hR hr hu
  have hAngular : ContDiffAt ℝ ∞ (fun _ : R3 =>
      sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i) y := contDiffAt_const
  have hLeading := (hR.inv hr).smul (hAngular.clm_apply hu)
  have hBase : ContDiffAt ℝ ∞ (fun x : R3 => (q,x)) y :=
    contDiffAt_const.prodMk contDiffAt_id
  have hDerivative : ContDiffAt ℝ ∞ (fderiv ℝ R) y := hR.fderiv_right (by simp)
  have hParam : ContDiffAt ℝ ∞ (fun x : R3 => ((q,x),fderiv ℝ R x)) y :=
    hBase.prodMk hDerivative
  have hCorrection : ContDiffAt ℝ ∞ (fun x : R3 =>
      referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
        ((q,x),fderiv ℝ R x) i) y :=
    (contDiff_referenceNativeMovingAdjointParametricCorrection hF hO hD g hg L (3/2 : ℝ) i).contDiffAt.comp y hParam
  have hIncluded := (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ)
      (by norm_num)).contDiff.contDiffAt.comp y (hCorrection.clm_apply hu)
  have hQuotient := contDiffAt_referenceHighAdjointMovingDifferenceQuotient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R y i hR hr hInv hp
  have hRemainder := hR.smul (hQuotient.clm_apply hu)
  exact ⟨hWeighted, by simpa only [Pi.smul_def',Pi.inv_apply] using hLeading,
    by simpa only [Function.comp_def] using hIncluded,
    by simpa only [Pi.smul_def'] using hRemainder⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighDensityFirstAction_normal_form_summands
