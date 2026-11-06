import Calderon.ActualDensityAngularBoundaryAction
import Calderon.MetricHessianQuadratic
import Calderon.WeightedIndexedCurvature

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
NORMALIZED-SCALAR-FRAME-EXPANSION-v001.md. Same actual normalized scalar Laplacian. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic SmoothMetricFrame MovingFrameConnection RadiusProfile
  ReferenceDensityBounds NormalizedPrincipalMetric ActualHorizontalNormBridge
  ActualNormalizedSecondMetricDrift PrincipalCommutator WeightedIndexedCurvature ConformalDepth

attribute [local irreducible] referenceDensityPrincipalFrameCoefficient
  referenceNormalizedPrincipalMatrix referenceCoFrameEntry referenceMetricGramFrame
  normalizedSecondDriftCoordinateJoint normalizedSecondDriftFrameJoint referenceConnectionFamily

theorem referenceDensityPrincipalFrameCoefficient_bilinear_contraction
    (g : MatrixField) (hg : IsAdmissibleMetric g) (g2 : MatrixField) (L q : ℝ) (y : R3)
    (B0 : R3 →L[ℝ] R3 →L[ℝ] ℝ) :
    (∑ k : Fin 3, ∑ l : Fin 3,
      referenceNormalizedPrincipalMatrix g g2 L q y k l * B0 (coordinateDirection k) (coordinateDirection l)) =
    ∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j *
        B0 (referenceMetricGramFrame g L (q,y) i) (referenceMetricGramFrame g L (q,y) j) := by
  have hB (k l : Fin 3) : B0 (coordinateDirection k) (coordinateDirection l) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        referenceCoFrameEntry g L k i (q,y) * referenceCoFrameEntry g L l j (q,y) *
          B0 (referenceMetricGramFrame g L (q,y) i) (referenceMetricGramFrame g L (q,y) j) := by
    calc
      _ = B0 (∑ i : Fin 3, referenceCoFrameEntry g L k i (q,y) • referenceMetricGramFrame g L (q,y) i)
          (∑ j : Fin 3, referenceCoFrameEntry g L l j (q,y) • referenceMetricGramFrame g L (q,y) j) :=
        congrArg₂ (fun X Y : R3 => B0 X Y)
          (coordinateDirection_eq_sum_referenceGramFrame g hg L q y k)
          (coordinateDirection_eq_sum_referenceGramFrame g hg L q y l)
      _ = _ := by
        simp only [Fin.sum_univ_three, map_add, map_smul, _root_.add_apply,
          _root_.smul_apply, smul_eq_mul]
        ring
  simp_rw [hB]
  simp only [referenceDensityPrincipalFrameCoefficient, Fin.sum_univ_three]
  ring

theorem normalizedSecondDriftFrame_linear_contraction
    (g : MatrixField) (hg : IsAdmissibleMetric g) (g2 : MatrixField) (L q : ℝ) (y : R3)
    (ell : R3 →L[ℝ] ℝ) :
    (∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) *
      ell (referenceMetricGramFrame g L (q,y) i)) =
    ∑ k : Fin 3, normalizedSecondDriftCoordinateJoint g g2 L k (q,y) * ell (coordinateDirection k) := by
  have hLinear (k : Fin 3) : ell (coordinateDirection k) =
      ∑ i : Fin 3, referenceCoFrameEntry g L k i (q,y) * ell (referenceMetricGramFrame g L (q,y) i) := by
    have h := congrArg ell (coordinateDirection_eq_sum_referenceGramFrame g hg L q y k)
    simpa only [map_sum, map_smul, smul_eq_mul] using h
  simp_rw [hLinear]
  simp only [normalizedSecondDriftFrameJoint, Fin.sum_univ_three]
  ring

theorem normalizedSecondLaplacian_eq_reference_frame_hessian_and_drift
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L q : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (y : R3) :
    normalizedSecondLaplacian g g2 L q f y =
    (∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j *
        coordinateHessian f (fun X Y => referenceConnectionFamily g L (q,y) X Y) y
          (referenceMetricGramFrame g L (q,y) i) (referenceMetricGramFrame g L (q,y) j)) +
    ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) *
      fderiv ℝ f y (referenceMetricGramFrame g L (q,y) i) := by
  let B0 := MetricVolume.coordinateHessianBilinear f (referenceConnectionFamily g L (q,y)) y
  have hPrincipal := referenceDensityPrincipalFrameCoefficient_bilinear_contraction g hg g2 L q y B0
  have hPrincipal' :
      (∑ k : Fin 3, ∑ l : Fin 3, referenceNormalizedPrincipalMatrix g g2 L q y k l *
        coordinateHessian f (fun X Y => referenceConnectionFamily g L (q,y) X Y) y
          (coordinateDirection k) (coordinateDirection l)) =
      ∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j *
        coordinateHessian f (fun X Y => referenceConnectionFamily g L (q,y) X Y) y
          (referenceMetricGramFrame g L (q,y) i) (referenceMetricGramFrame g L (q,y) j) := by
    simpa only [B0, MetricVolume.coordinateHessianBilinear_apply] using hPrincipal
  have hDrift := normalizedSecondDriftFrame_linear_contraction g hg g2 L q y (fderiv ℝ f y)
  have hTotal := congrArg₂ (fun a b : ℝ => a+b) hPrincipal' hDrift.symm
  exact (normalizedSecondLaplacian_eq_reference_hessian_and_drift g g2 hg2 L q f hf y).trans hTotal

theorem normalizedSecondLaplacian_eq_reference_frame_derivatives
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L q : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (y : R3) :
    normalizedSecondLaplacian g g2 L q f y =
    (∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j *
        (fderiv ℝ (fun z => fderiv ℝ f z (referenceMetricGramFrame g L (q,z) j)) y
            (referenceMetricGramFrame g L (q,y) i) -
          ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
            (referenceMetricGramFrame g L (q,y) i) k j *
            fderiv ℝ f y (referenceMetricGramFrame g L (q,y) k))) +
    ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) *
      fderiv ℝ f y (referenceMetricGramFrame g L (q,y) i) := by
  have hFrame (i j : Fin 3) : coordinateHessian f
      (fun X Y => referenceConnectionFamily g L (q,y) X Y) y
      (referenceMetricGramFrame g L (q,y) i) (referenceMetricGramFrame g L (q,y) j) =
      fderiv ℝ (fun z => fderiv ℝ f z (referenceMetricGramFrame g L (q,z) j)) y
          (referenceMetricGramFrame g L (q,y) i) -
        ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
          (referenceMetricGramFrame g L (q,y) i) k j *
          fderiv ℝ f y (referenceMetricGramFrame g L (q,y) k) := by
    have h := referenceFrameDerivative_df_eq_hessian_add_connection g hg L q f hf y i j
    linarith
  simpa only [hFrame] using
    normalizedSecondLaplacian_eq_reference_frame_hessian_and_drift g g2 hg hg2 L q f hf y

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityPrincipalFrameCoefficient_bilinear_contraction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.normalizedSecondDriftFrame_linear_contraction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.normalizedSecondLaplacian_eq_reference_frame_hessian_and_drift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.normalizedSecondLaplacian_eq_reference_frame_derivatives
