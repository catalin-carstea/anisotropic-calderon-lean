import Calderon.SphereSobolevShiftedPhysicalDegree
import Calderon.SphereSobolevOrderOneRotation
import Calderon.SphereSobolevCoordinateMultiplier
import Calderon.ActualDensityAngularBoundaryAction
import Calderon.ActualFirstCorrectionParameterJets
import Calderon.ActualNativeMovingRadiusTrace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual finite native J; compact derivative parameter before p. The physical
P/canonical harmonic dictionary is an explicit separate graph, not a premise. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic

def sphereSobolevAngularCoordinateTransposeL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (i : Fin 3) : SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
  -(∑ j : Fin 3, (sphereSobolevRotationL s j i).comp
    (sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single j 1))) +
  (sphereSobolevShiftedDegreeL s).comp
    (sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single i 1))

end OAI.AnisotropicCalderon.SphereHarmonic
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  ActualNormalizedSecondMetricDrift NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge


def referenceNativeMovingAdjointParametricCorrection
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L s : ℝ) (z : (ℝ × R3) × (R3 →L[ℝ] ℝ)) (i : Fin 3) :
    SphereSobolev s →L[ℝ] SphereSobolev s :=
  (sphereSobolevRadialDriftAdjointL hF hO hD s (referenceCenterDrift g L z.1.1 z.1.2)).comp
    (sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single i 1)) +
  z.2 (conformalReferenceGramFrameOperatorJoint g L z.1 (coordinateVector i)) •
    sphereSobolevRadialDriftAdjointL hF hO hD s (referenceCenterDrift g L z.1.1 z.1.2)


def referenceNativeMovingAdjointParametricJ
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g g2 : MatrixField) (L : ℝ) (z : (ℝ × R3) × (R3 →L[ℝ] ℝ)) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L z.1.1 z.1.2 i j •
    ((sphereSobolevAngularCoordinateTransposeL hF hO hD 1 i).comp
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 1 z j) +
      (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0 z i).comp
        (sphereSobolevAngularCoordinateTransposeL hF hO hD 1 j))) +
  ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i z.1 •
    sphereSobolevAngularCoordinateTransposeL hF hO hD 1 i

attribute [local irreducible] sphereSobolevAngularCoordinateTransposeL
  referenceNativeMovingAdjointParametricCorrection referenceNativeMovingAdjointParametricJ
  referenceDensityPrincipalFrameCoefficient sphereSobolevRadialDriftAdjointL
  sphereSobolevLinearCoordinateMulL

lemma referenceRadius_mul_horizontalLogDerivative_eq_fderiv
    (g : MatrixField) (L q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (y : R3) (hr : R y ≠ 0) (i : Fin 3) :
    R y * referenceRadiusHorizontalLogDerivative g L q R y i =
      fderiv ℝ R y (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)) := by
  unfold referenceRadiusHorizontalLogDerivative
  rw [fderiv_log_radius_apply R hR y _ hr]
  calc
    _ = (R y * (R y)⁻¹) *
        fderiv ℝ R y (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hr,one_mul]

lemma contDiff_referenceNativeMovingAdjointParametricCorrection
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L s : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (referenceNativeMovingAdjointParametricCorrection hF hO hD g L s · i) := by
  have hD : ContDiff ℝ ∞ (fun z : (ℝ × R3) × (R3 →L[ℝ] ℝ) =>
      sphereSobolevRadialDriftAdjointL hF hO hD s (referenceCenterDrift g L z.1.1 z.1.2)) :=
    ((contDiff_sphereSobolevRadialDriftAdjointL hF hO hD s).of_le le_top).comp
      ((contDiff_referenceCenterDrift_joint g hg L).comp contDiff_fst)
  have hFrame : ContDiff ℝ ∞ (fun z : (ℝ × R3) × (R3 →L[ℝ] ℝ) =>
      conformalReferenceGramFrameOperatorJoint g L z.1) :=
    (contDiff_conformalReferenceGramFrameOperatorJoint g hg L).comp contDiff_fst
  have hWeight : ContDiff ℝ ∞ (fun z : (ℝ × R3) × (R3 →L[ℝ] ℝ) =>
      z.2 (conformalReferenceGramFrameOperatorJoint g L z.1 (coordinateVector i))) :=
    contDiff_snd.clm_apply (hFrame.clm_apply contDiff_const)
  unfold referenceNativeMovingAdjointParametricCorrection
  exact (hD.clm_comp contDiff_const).add (hWeight.smul hD)

lemma contDiff_referenceNativeMovingAdjointParametricJ
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) : ContDiff ℝ ∞ (referenceNativeMovingAdjointParametricJ hF hO hD g g2 L) := by
  have hQ (i j : Fin 3) : ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      referenceDensityPrincipalFrameCoefficient g g2 L z.1 z.2 i j) := by
    unfold referenceDensityPrincipalFrameCoefficient
    exact ContDiff.sum (fun k _ => ContDiff.sum (fun l _ =>
      ((contDiff_referenceNormalizedPrincipalMatrix_entry_joint g g2 hg hg2 L k l).mul
        (contDiff_referenceCoFrameEntry g hg L k i)).mul
          (contDiff_referenceCoFrameEntry g hg L l j)))
  have hF0 (i : Fin 3) :=
    contDiff_referenceNativeMovingAdjointParametricCorrection hF hO hD g hg L 0 i
  have hF1 (i : Fin 3) :=
    contDiff_referenceNativeMovingAdjointParametricCorrection hF hO hD g hg L 1 i
  have hB (i : Fin 3) : ContDiff ℝ ∞ (fun z : (ℝ × R3) × (R3 →L[ℝ] ℝ) =>
      normalizedSecondDriftFrameJoint g g2 L i z.1) :=
    (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).comp contDiff_fst
  unfold referenceNativeMovingAdjointParametricJ
  exact (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
      ((hQ i j).comp contDiff_fst).smul
        ((contDiff_const.clm_comp (hF1 j)).add ((hF0 i).clm_comp contDiff_const))))).add
    (ContDiff.sum (fun i _ => (hB i).smul contDiff_const))

lemma exists_referenceNativeMovingAdjointParametricJ_uniform_bound
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ K,
      ∀ ell : R3 →L[ℝ] ℝ, ‖ell‖ ≤ 1 →
        ‖referenceNativeMovingAdjointParametricJ hF hO hD g g2 L ((q,y),ell)‖ ≤ CJ := by
  have hCompact : IsCompact (((Icc (0 : ℝ) 1) ×ˢ K) ×ˢ
      closedBall (0 : R3 →L[ℝ] ℝ) 1) :=
    (isCompact_Icc.prod hK).prod (isCompact_closedBall _ _)
  have hNorm : Continuous (fun z : (ℝ × R3) × (R3 →L[ℝ] ℝ) =>
      ‖referenceNativeMovingAdjointParametricJ hF hO hD g g2 L z‖) :=
    (continuous_norm (E := SphereSobolev 1 →L[ℝ] SphereSobolev 0)).comp
      (contDiff_referenceNativeMovingAdjointParametricJ hF hO hD g g2 hg hg2 L).continuous
  obtain ⟨C,hC⟩ := hCompact.exists_bound_of_continuousOn
    (f := fun z : (ℝ × R3) × (R3 →L[ℝ] ℝ) =>
      ‖referenceNativeMovingAdjointParametricJ hF hO hD g g2 L z‖) hNorm.continuousOn
  refine ⟨max 1 C,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro q hq y hy ell hell
  have hEll : ell ∈ closedBall (0 : R3 →L[ℝ] ℝ) 1 := by
    simpa only [mem_closedBall,dist_zero_right] using hell
  have hValue : ‖referenceNativeMovingAdjointParametricJ hF hO hD g g2 L ((q,y),ell)‖ ≤ C := by
    have hAbs : |‖referenceNativeMovingAdjointParametricJ hF hO hD g g2 L ((q,y),ell)‖| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC ((q,y),ell) ⟨⟨hq,hy⟩,hEll⟩
    exact (le_abs_self ‖referenceNativeMovingAdjointParametricJ hF hO hD g g2 L ((q,y),ell)‖).trans hAbs
  exact hValue.trans (le_max_right _ _)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevAngularCoordinateTransposeL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNativeMovingAdjointParametricCorrection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNativeMovingAdjointParametricJ
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadius_mul_horizontalLogDerivative_eq_fderiv
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceNativeMovingAdjointParametricCorrection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceNativeMovingAdjointParametricJ
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceNativeMovingAdjointParametricJ_uniform_bound
