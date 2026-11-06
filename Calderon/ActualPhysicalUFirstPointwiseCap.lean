import Calderon.ActualPhysicalUFirstPointwisePreparation
import Calderon.ActualPhysicalUFirstCaps
import Calderon.ActualFinitePhysicalModelErrorDictionary
import Calderon.FiniteCoreSobolevDerivativeEnergy
import Calderon.FiniteCoreH1BesselNorm
import Calderon.ActualFiniteHarmonicModelHorizontalProfileComparison
import Calderon.ActualHorizontalGeometry
import Calderon.ActualDensityPrincipalFrameSmoothness
import Calderon.ActualNormalizedSecondMetricDrift
import Calderon.ActualRadiusThreeJetProfileRoom
import Calderon.SphereSobolevInclusion

/-! Author: Claude (Opus 5.5), v033. Expansion: output/MATHEMATICS.md.
I3 (chain/product), I4 (frame/coordinate derivative), I5 (graph identity of the core input),
the six literal word bounds and the uniform pointwise cap of the actual `nativeUFirstOut`.
All caps are produced internally from existing producers; no callback or new hypothesis. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore
  ActualFiniteHarmonicModel ActualFiniteHarmonicAmbient SpectralCoreRegularity
  SpectralWeightedGraph SphereHilbertDecomposition NormalCoordinatesFrame SmoothMetricFrame MovingFrameConnection AmbientReferenceRaising
  ActualReferenceModelTrace ActualReferenceParallelRaising ActualPhysicalMixedNative
  ActualPhysicalPureAngular ActualNormalizedSecondMetricDrift
  ActualNormalizedSecondDriftAngularAllocation ActualNormalizedSecondModelErrorAssembly
  ReferenceDensityBounds NormalizedPrincipalMetric ConformalDepth RadiusProfile
  AngularShiftGraph HarmonicDerivativeOperator SmoothSphereRotationProjection
  PrincipalCommutator BoundedAngularShift ActualHorizontalNormBridge ActualHigherRadiusProfile

open ReferenceWeightedApproximation ActualBalancedFirstPrincipalError SectionFiveErrorForms

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevZeroEquiv
  sphereSobolevRotationL sphereSobolevShiftedDegreeL finiteCoreSobolevLift
  coreReferenceInput referenceNativeMovingAdjointParametricCorrection
  referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint
  referenceFrameConnectionCoefficient referenceMetricGramFrame referenceRadiusHorizontalLogDerivative
  nativeOneHorizontalAngularL nativeOneShiftedDegreeL nativeOneWeightedHorizontalAction
  nativeFirstCorrectionLift nativeUFirstWord nativeUFirstOut

-- Root reuses actualSol validated prelude: cache only the original canonical class data; do not replace norms or metrics.
@[instance_reducible] private def pointwiseOriginalParameterNormed :
    NormedAddCommGroup ((ℝ × R3) × (R3 →L[ℝ] ℝ)) := inferInstance
@[instance_reducible] private def pointwiseOriginalParameterModule :
    NormedSpace ℝ ((ℝ × R3) × (R3 →L[ℝ] ℝ)) := inferInstance
@[instance_reducible] private def pointwiseOriginalCorrectionNormed :
    NormedAddCommGroup (SphereSobolev 0 →L[ℝ] SphereSobolev 0) := inferInstance
@[instance_reducible] private def pointwiseOriginalCorrectionModule :
    NormedSpace ℝ (SphereSobolev 0 →L[ℝ] SphereSobolev 0) := inferInstance
@[instance_reducible] private def pointwiseParameterNormed :
    NormedAddCommGroup ((ℝ × R3) × (R3 →L[ℝ] ℝ)) := pointwiseOriginalParameterNormed
attribute [local instance] pointwiseParameterNormed
@[instance_reducible] private def pointwiseParameterModule :
    NormedSpace ℝ ((ℝ × R3) × (R3 →L[ℝ] ℝ)) := pointwiseOriginalParameterModule
attribute [local instance] pointwiseParameterModule
@[instance_reducible] private def pointwiseCorrectionNormed :
    NormedAddCommGroup (SphereSobolev 0 →L[ℝ] SphereSobolev 0) := pointwiseOriginalCorrectionNormed
attribute [local instance] pointwiseCorrectionNormed
@[instance_reducible] private def pointwiseCorrectionModule :
    NormedSpace ℝ (SphereSobolev 0 →L[ℝ] SphereSobolev 0) := pointwiseOriginalCorrectionModule
attribute [local instance] pointwiseCorrectionModule
private theorem pointwiseParameterNormed_canonical : pointwiseParameterNormed = pointwiseOriginalParameterNormed := rfl
private theorem pointwiseParameterModule_canonical : pointwiseParameterModule = pointwiseOriginalParameterModule := rfl
private theorem pointwiseCorrectionNormed_canonical : pointwiseCorrectionNormed = pointwiseOriginalCorrectionNormed := rfl
private theorem pointwiseCorrectionModule_canonical : pointwiseCorrectionModule = pointwiseOriginalCorrectionModule := rfl

-- Root caches original value and first spatial-derivative structures, with exact rfl bridges.
@[instance_reducible] private def pointwiseOriginalValueNormed :
    NormedAddCommGroup (SphereSobolev 1) := inferInstance
@[instance_reducible] private def pointwiseOriginalValueModule :
    NormedSpace ℝ (SphereSobolev 1) := inferInstance
@[instance_reducible] private def pointwiseOriginalSpatialNormed :
    NormedAddCommGroup (R3 →L[ℝ] SphereSobolev 1) := inferInstance
@[instance_reducible] private def pointwiseOriginalSpatialModule :
    NormedSpace ℝ (R3 →L[ℝ] SphereSobolev 1) := inferInstance
@[instance_reducible] private def pointwiseValueNormed :
    NormedAddCommGroup (SphereSobolev 1) := pointwiseOriginalValueNormed
attribute [local instance] pointwiseValueNormed
@[instance_reducible] private def pointwiseValueModule :
    NormedSpace ℝ (SphereSobolev 1) := pointwiseOriginalValueModule
attribute [local instance] pointwiseValueModule
@[instance_reducible] private def pointwiseSpatialNormed :
    NormedAddCommGroup (R3 →L[ℝ] SphereSobolev 1) := pointwiseOriginalSpatialNormed
attribute [local instance] pointwiseSpatialNormed
@[instance_reducible] private def pointwiseSpatialModule :
    NormedSpace ℝ (R3 →L[ℝ] SphereSobolev 1) := pointwiseOriginalSpatialModule
attribute [local instance] pointwiseSpatialModule
private theorem pointwiseValueNormed_canonical : pointwiseValueNormed = pointwiseOriginalValueNormed := rfl
private theorem pointwiseValueModule_canonical : pointwiseValueModule = pointwiseOriginalValueModule := rfl
private theorem pointwiseSpatialNormed_canonical : pointwiseSpatialNormed = pointwiseOriginalSpatialNormed := rfl
private theorem pointwiseSpatialModule_canonical : pointwiseSpatialModule = pointwiseOriginalSpatialModule := rfl

attribute [local irreducible] coreDirectionalDerivative coreWeightOperator

/-! ### Six literal word bounds -/

/-- Pointwise word bound under the actual caps at `z = ((q,y), dR y)` (all chosen by the final
theorem from existing producers). -/
theorem norm_nativeUFirstWord_le (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g) (L q δ A : ℝ)
    (p : ℕ) (hδ : 0 < δ) (hA : 0 < A) (F0 : smoothCompactFiniteSphereCore hO hD)
    (i j : Fin 3) (y : R3) {M Mg P Cc β : ℝ} (hM : 0 ≤ M) (hMg : 0 ≤ Mg) (hP : 0 ≤ P)
    (hCc : 0 ≤ Cc) (hβ : 1 ≤ β)
    (hC0 : ∀ k, ‖referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y) k‖ ≤ M)
    (hC1 : ∀ k, ‖referenceNativeMovingAdjointParametricCorrection hF hO hD g L 1
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y) k‖ ≤ M)
    (hdC0 : ∀ k, ‖fderiv ℝ (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0 · k)
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y)‖ ≤ M)
    (hH : ‖fderiv ℝ (fderiv ℝ (referenceRadius δ A p L)) y‖ ≤ P)
    (hfe : ∀ a k, ‖frameEntry g L a k (q,y)‖ ≤ Mg)
    (hΓ : ∀ a b c, ‖referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) a) b c‖ ≤ Mg)
    (hf : ∀ a, ‖referenceRadiusHorizontalLogDerivative g L q (referenceRadius δ A p L) y a‖ ≤
      P * Cc * β) :
    ‖nativeUFirstWord hF hO hD g hg L q δ A p hδ hA F0 i j y‖ ≤
      2 * (M * Mg) *
          (∑ k : Fin 3, ‖(coreDirectionalDerivative hO hD (coordinateDirection k) F0).val y‖) +
        ufirstWordCoeff M Mg P Cc * (β * ‖finiteCoreSobolevLift hO hD 1 F0 y‖) := by
  have hR : ContDiff ℝ ∞ (referenceRadius δ A p L) :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ A p L hδ hA
  have hcI := ufirstInclusionNorm_nonneg
  have hcA := ufirstAngularNorm_nonneg
  have hcD := ufirstDegreeNorm_nonneg
  have hCe := ufirstDirectionNorm_nonneg
  have hm0 := norm_nonneg (finiteCoreSobolevLift hO hD 1 F0 y)
  have hmβ : ‖finiteCoreSobolevLift hO hD 1 F0 y‖ ≤ β * ‖finiteCoreSobolevLift hO hD 1 F0 y‖ := by
    nlinarith
  have hPCβ : 0 ≤ P * Cc * β := mul_nonneg (mul_nonneg hP hCc) (by linarith)
  have hI : ∀ w : SphereSobolev 1,
      ‖sphereSobolevInclusionL 1 0 (by norm_num) w‖ ≤ ufirstInclusionNorm * ‖w‖ :=
    fun w => ContinuousLinearMap.le_opNorm _ _
  have hDeg : ∀ w : SphereSobolev 1, ‖nativeOneShiftedDegreeL w‖ ≤ ufirstDegreeNorm * ‖w‖ :=
    fun w => ContinuousLinearMap.le_opNorm _ _
  have hAng : ∀ a, ∀ w : SphereSobolev 1,
      ‖nativeOneHorizontalAngularL g L q y a w‖ ≤ (Mg * ufirstAngularNorm) * ‖w‖ :=
    fun a w => (nativeOneHorizontalAngularL g L q y a).le_of_opNorm_le
      (norm_nativeOneHorizontalAngularL_le g L q y a (hΓ a)) w
  have hV : ∀ k, ‖nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 k y‖ ≤
      M * ‖finiteCoreSobolevLift hO hD 1 F0 y‖ := by
    intro k
    simpa only [nativeFirstCorrectionLift] using
      ((referenceNativeMovingAdjointParametricCorrection hF hO hD g L 1
        ((q,y),fderiv ℝ (referenceRadius δ A p L) y) k).le_of_opNorm_le (hC1 k)
          (finiteCoreSobolevLift hO hD 1 F0 y))
  have hIV : ∀ k, ‖sphereSobolevInclusionL 1 0 (by norm_num)
      (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 k y)‖ ≤
      ufirstInclusionNorm * (M * ‖finiteCoreSobolevLift hO hD 1 F0 y‖) :=
    fun k => (hI _).trans (mul_le_mul_of_nonneg_left (hV k) hcI)
  have hDX := fun a => norm_inclusion_fderiv_finiteCoreSobolevLift_frame_le hO hD g L q F0 y a
    (hfe a)
  -- (1) derivative of the first correction along `X_i`
  have h1 : ‖sphereSobolevInclusionL 1 0 (by norm_num)
      (fderiv ℝ (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 j) y
        (referenceMetricGramFrame g L (q,y) i))‖ ≤
      M * (Mg * ∑ k : Fin 3,
          ‖(coreDirectionalDerivative hO hD (coordinateDirection k) F0).val y‖) +
        M * (1 + P) * (Mg * ufirstDirectionNorm) *
          (ufirstInclusionNorm * ‖finiteCoreSobolevLift hO hD 1 F0 y‖) := by
    have hMP : 0 ≤ M * (1 + P) := mul_nonneg hM (by linarith)
    refine (norm_inclusion_fderiv_nativeFirstCorrectionLift_le hF hO hD g hg L q
      (referenceRadius δ A p L) hR F0 j y (referenceMetricGramFrame g L (q,y) i) hM hP
      (hC0 j) (hdC0 j) hH).trans (add_le_add (mul_le_mul_of_nonneg_left (hDX i) hM) ?_)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_referenceMetricGramFrame_le g L q y i
      (hfe i)) hMP) (hI _) (norm_nonneg _) (mul_nonneg hMP (mul_nonneg hMg hCe))
  -- (2) angular connection on the first correction
  have h2 : ‖nativeOneHorizontalAngularL g L q y i
      (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 j y)‖ ≤
      (Mg * ufirstAngularNorm) * (M * ‖finiteCoreSobolevLift hO hD 1 F0 y‖) :=
    (hAng i _).trans (mul_le_mul_of_nonneg_left (hV j) (mul_nonneg hMg hcA))
  -- (3) `f_i •` physical degree on the first correction
  have h3 : ‖referenceRadiusHorizontalLogDerivative g L q (referenceRadius δ A p L) y i •
      nativeOneShiftedDegreeL
        (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 j y)‖ ≤
      (P * Cc * β) * (ufirstDegreeNorm * (M * ‖finiteCoreSobolevLift hO hD 1 F0 y‖)) := by
    rw [norm_smul]
    exact mul_le_mul (hf i) ((hDeg _).trans (mul_le_mul_of_nonneg_left (hV j) hcD))
      (norm_nonneg _) hPCβ
  -- (4) correction applied to the actual core input
  have hIn : ‖sphereSobolevZeroEquiv hO hD
      ((coreReferenceInput hO hD g hg L q δ A p j hδ hA F0).val y)‖ ≤
      Mg * (∑ k : Fin 3, ‖(coreDirectionalDerivative hO hD (coordinateDirection k) F0).val y‖) +
        (Mg * ufirstAngularNorm) * ‖finiteCoreSobolevLift hO hD 1 F0 y‖ +
        (P * Cc * β) * (ufirstDegreeNorm * ‖finiteCoreSobolevLift hO hD 1 F0 y‖) := by
    rw [zeroEquiv_coreReferenceInput_eq_expanded hO hD g hg L q δ A p hδ hA F0 y j]
    refine (norm_add_add_le' _ _ _).trans (add_le_add (add_le_add (hDX j) (hAng j _)) ?_)
    rw [norm_smul]
    exact mul_le_mul (hf j) (hDeg _) (norm_nonneg _) hPCβ
  have h4 : ‖referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y) i
      (sphereSobolevZeroEquiv hO hD ((coreReferenceInput hO hD g hg L q δ A p j hδ hA F0).val y))‖ ≤
      M * (Mg * (∑ k : Fin 3,
          ‖(coreDirectionalDerivative hO hD (coordinateDirection k) F0).val y‖) +
        (Mg * ufirstAngularNorm) * ‖finiteCoreSobolevLift hO hD 1 F0 y‖ +
        (P * Cc * β) * (ufirstDegreeNorm * ‖finiteCoreSobolevLift hO hD 1 F0 y‖)) :=
    ((referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y) i).le_of_opNorm_le (hC0 i) _).trans
      (mul_le_mul_of_nonneg_left hIn hM)
  -- (5) connection sum on the first corrections
  have h5 : ‖∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j •
      sphereSobolevInclusionL 1 0 (by norm_num)
        (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 k y)‖ ≤
      Mg * (ufirstInclusionNorm * (M * ‖finiteCoreSobolevLift hO hD 1 F0 y‖)) +
        Mg * (ufirstInclusionNorm * (M * ‖finiteCoreSobolevLift hO hD 1 F0 y‖)) +
        Mg * (ufirstInclusionNorm * (M * ‖finiteCoreSobolevLift hO hD 1 F0 y‖)) := by
    have hs := (norm_sum_le _ _).trans (Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) =>
      (show ‖referenceFrameConnectionCoefficient g L q y
          (referenceMetricGramFrame g L (q,y) i) k j •
        sphereSobolevInclusionL 1 0 (by norm_num)
          (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 k y)‖ ≤
        Mg * (ufirstInclusionNorm * (M * ‖finiteCoreSobolevLift hO hD 1 F0 y‖)) by
          rw [norm_smul]; exact mul_le_mul (hΓ i k j) (hIV k) (norm_nonneg _) hMg))
    simpa only [Fin.sum_univ_three] using hs
  -- (6) correction on the included first correction
  have h6 : ‖referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y) i
      (sphereSobolevInclusionL 1 0 (by norm_num)
        (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 j y))‖ ≤
      M * (ufirstInclusionNorm * (M * ‖finiteCoreSobolevLift hO hD 1 F0 y‖)) :=
    ((referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y) i).le_of_opNorm_le (hC0 i) _).trans
      (mul_le_mul_of_nonneg_left (hIV j) hM)
  -- conversion `m ≤ β m` for the `m`-coefficient
  have hγ : 0 ≤ M * (1 + P) * (Mg * ufirstDirectionNorm) * ufirstInclusionNorm +
      2 * (M * Mg * ufirstAngularNorm) + 3 * (Mg * ufirstInclusionNorm * M) +
      M * ufirstInclusionNorm * M :=
    add_nonneg (add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hM (by linarith)) (mul_nonneg hMg hCe)) hcI)
      (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hM hMg) hcA)))
      (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hMg hcI) hM)))
      (mul_nonneg (mul_nonneg hM hcI) hM)
  have hconv := mul_le_mul_of_nonneg_left hmβ hγ
  unfold nativeUFirstWord nativeOneWeightedHorizontalAction
  refine (norm_add_add_add_sub_add_le _ _ _ _ _ _).trans
    ((add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5) h6).trans ?_)
  unfold ufirstWordCoeff
  linarith [hconv]

/-! ### Output bound -/

theorem norm_nativeUFirstOut_le (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g) (g2 : MatrixField)
    (L q δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A) (F0 : smoothCompactFiniteSphereCore hO hD)
    (y : R3) {M Mg P Cc β BQ Bb : ℝ} (hM : 0 ≤ M) (hMg : 0 ≤ Mg) (hP : 0 ≤ P)
    (hCc : 0 ≤ Cc) (hβ : 1 ≤ β) (hBQ0 : 0 ≤ BQ) (hBb0 : 0 ≤ Bb)
    (hC0 : ∀ k, ‖referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y) k‖ ≤ M)
    (hC1 : ∀ k, ‖referenceNativeMovingAdjointParametricCorrection hF hO hD g L 1
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y) k‖ ≤ M)
    (hdC0 : ∀ k, ‖fderiv ℝ (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0 · k)
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y)‖ ≤ M)
    (hH : ‖fderiv ℝ (fderiv ℝ (referenceRadius δ A p L)) y‖ ≤ P)
    (hfe : ∀ a k, ‖frameEntry g L a k (q,y)‖ ≤ Mg)
    (hΓ : ∀ a b c, ‖referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) a) b c‖ ≤ Mg)
    (hf : ∀ a, ‖referenceRadiusHorizontalLogDerivative g L q (referenceRadius δ A p L) y a‖ ≤
      P * Cc * β)
    (hQ : ∀ a b, ‖referenceDensityPrincipalFrameCoefficient g g2 L q y a b‖ ≤ BQ)
    (hb : ∀ a, ‖normalizedSecondDriftFrameJoint g g2 L a (q,y)‖ ≤ Bb) :
    ‖nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0 y‖ ≤
      referenceRadius δ A p L y *
        ((9 * (BQ * (2 * (M * Mg)))) *
            (∑ k : Fin 3, ‖(coreDirectionalDerivative hO hD (coordinateDirection k) F0).val y‖) +
          (9 * (BQ * ufirstWordCoeff M Mg P Cc) + 3 * (Bb * (ufirstInclusionNorm * M))) *
            (β * ‖finiteCoreSobolevLift hO hD 1 F0 y‖)) := by
  have hr : 0 ≤ referenceRadius δ A p L y := (referenceRadius_pos δ A p L y hδ hA).le
  have hcI := ufirstInclusionNorm_nonneg
  have hm0 := norm_nonneg (finiteCoreSobolevLift hO hD 1 F0 y)
  have hmβ : ‖finiteCoreSobolevLift hO hD 1 F0 y‖ ≤ β * ‖finiteCoreSobolevLift hO hD 1 F0 y‖ := by
    nlinarith
  have hWord := fun a b => norm_nativeUFirstWord_le hF hO hD g hg L q δ A p hδ hA F0 a b y
    hM hMg hP hCc hβ hC0 hC1 hdC0 hH hfe hΓ hf
  have hLift (a : Fin 3) :
      ‖nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 a y‖ ≤
        M * ‖finiteCoreSobolevLift hO hD 1 F0 y‖ := by
    simpa only [nativeFirstCorrectionLift] using
      ((referenceNativeMovingAdjointParametricCorrection hF hO hD g L 1
        ((q,y),fderiv ℝ (referenceRadius δ A p L) y) a).le_of_opNorm_le (hC1 a)
          (finiteCoreSobolevLift hO hD 1 F0 y))
  have hS1 : ‖∑ a : Fin 3, ∑ b : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y a b •
      nativeUFirstWord hF hO hD g hg L q δ A p hδ hA F0 a b y‖ ≤
      ∑ a : Fin 3, ∑ b : Fin 3, BQ * (2 * (M * Mg) *
          (∑ k : Fin 3, ‖(coreDirectionalDerivative hO hD (coordinateDirection k) F0).val y‖) +
        ufirstWordCoeff M Mg P Cc * (β * ‖finiteCoreSobolevLift hO hD 1 F0 y‖)) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun b _ => by
        rw [norm_smul]; exact mul_le_mul (hQ a b) (hWord a b) (norm_nonneg _) hBQ0))
  have hS2 : ‖∑ a : Fin 3, normalizedSecondDriftFrameJoint g g2 L a (q,y) •
      sphereSobolevInclusionL 1 0 (by norm_num)
        (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 a y)‖ ≤
      ∑ a : Fin 3, Bb * (ufirstInclusionNorm * (M * ‖finiteCoreSobolevLift hO hD 1 F0 y‖)) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => by
      rw [norm_smul]
      refine mul_le_mul (hb a) ?_ (norm_nonneg _) hBb0
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (hLift a) hcI))
  simp only [Fin.sum_univ_three] at hS1 hS2
  have hconv := mul_le_mul_of_nonneg_left hmβ
    (show 0 ≤ 3 * (Bb * (ufirstInclusionNorm * M)) by
      exact mul_nonneg (by norm_num) (mul_nonneg hBb0 (mul_nonneg hcI hM)))
  unfold nativeUFirstOut
  rw [LinearIsometryEquiv.norm_map]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hr, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ hr
  simp only [Fin.sum_univ_three]
  linarith [hS1, hS2, hconv]

/-! ### Energy inequalities -/

section UFirstGradientEnergy

-- Proof-local transparency only: these exact core operators are not redefined.

private lemma ufirst_principal_slots_le_sourceNormSquareIntegrand
    (β : ℝ) (hβ : 0 ≤ β) (G0 GH : Fin 3 → SphereL2) (U1 U3 : SphereL2) :
    (∑ k : Fin 3, ‖G0 k‖ ^ 2) + β ^ 2 * ‖U1‖ ^ 2 ≤
      sourceNormSquareIntegrand β G0 U1 GH U3 := by
  have hHalf : 0 ≤ β⁻¹ * (∑ k : Fin 3, ‖GH k‖ ^ 2) :=
    mul_nonneg (inv_nonneg.mpr hβ) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hThree : 0 ≤ β * ‖U3‖ ^ 2 := mul_nonneg hβ (sq_nonneg _)
  unfold sourceNormSquareIntegrand
  exact (le_add_of_nonneg_right hHalf).trans (le_add_of_nonneg_right hThree)

lemma gradient_energy_le_finiteCoreSourceEnergy (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (β : ℝ) (hβ : 0 ≤ β) (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) :
    (∑ k : Fin 3, ‖(coreDirectionalDerivative hO hD (coordinateDirection k) F).val x‖ ^ 2) +
        β ^ 2 * ‖(coreWeightOperator hO hD (besselWeight 1) F).val x‖ ^ 2 ≤
      finiteCoreSourceEnergy hO hD β F x := by
  let G0 : Fin 3 → SphereL2 := fun k =>
    (coreDirectionalDerivative hO hD (coordinateDirection k) F).val x
  let U1 : SphereL2 := (coreWeightOperator hO hD (besselWeight 1) F).val x
  let GH : Fin 3 → SphereL2 := fun k =>
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
      (coreDirectionalDerivative hO hD (coordinateDirection k) F)).val x
  let U3 : SphereL2 := (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F).val x
  have hEnergy : finiteCoreSourceEnergy hO hD β F x =
      sourceNormSquareIntegrand β G0 U1 GH U3 := by
    rfl
  have hPrincipal : (∑ k : Fin 3, ‖G0 k‖ ^ 2) + β ^ 2 * ‖U1‖ ^ 2 ≤
      sourceNormSquareIntegrand β G0 U1 GH U3 :=
    ufirst_principal_slots_le_sourceNormSquareIntegrand β hβ G0 GH U1 U3
  exact hPrincipal.trans hEnergy.symm.le

end UFirstGradientEnergy


/-! ### Uniform pointwise cap of the actual UFirst output -/

/-- Exact endpoint: `C_UF` is chosen from fixed data before `q, δ, A, p, η, BF, F0, y`. -/
private lemma ufirst_square_profile_finish {N r X C E : ℝ}
    (hN : N ≤ (r * X) ^ 2) (hX : X ^ 2 ≤ C * E) (hE : 0 ≤ E) :
    N ≤ (1 + C) * r ^ 2 * E := by
  have hRE : 0 ≤ r ^ 2 * E := mul_nonneg (sq_nonneg r) hE
  calc
    N ≤ (r * X) ^ 2 := hN
    _ = r ^ 2 * X ^ 2 := by ring
    _ ≤ r ^ 2 * (C * E) := mul_le_mul_of_nonneg_left hX (sq_nonneg r)
    _ ≤ (1 + C) * r ^ 2 * E := by nlinarith [hRE]

theorem exists_nativeUFirstOut_uniform_pointwise_cap (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (L : ℝ)
    (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C_UF : ℝ, 0 < C_UF ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ δ A : ℝ, ∀ (hδ : 0 < δ), δ ≤ 1 →
      ∀ (hA : 0 < A), ∀ p : ℕ, 2 ≤ p → ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ BF : ℝ, 1 ≤ BF →
      ∀ F0 : smoothCompactFiniteSphereCore hO hD, ∀ y ∈ K,
        BF ≤ actualReferenceBeta g L q δ A p y →
        ‖fderiv ℝ (referenceRadius δ A p L) y‖ ≤ 1 →
        referenceRadius δ A p L y * actualReferenceBeta g L q δ A p y ^ 2 ≤ η →
        ‖nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0 y‖ ^ 2 ≤
          C_UF * referenceRadius δ A p L y ^ 2 *
            finiteCoreReferenceProfileEnergy hO hD g hg L q
              (actualReferenceBeta g L q δ A p y) F0 y := by
  obtain ⟨room⟩ := exists_referenceRadiusThreeJetProfileRoom g hg L hL K hK
  obtain ⟨M, hM1, hMcap⟩ := exists_correction_compact_caps hF hO hD g hg L K hK
  obtain ⟨Cc, hCc0, hCc⟩ := exists_conformalFrame_cap g hg L K hK
  obtain ⟨Mg, hMg1, hgeo⟩ := exists_reference_geometry_uniform_bounds g hg L K hK
  obtain ⟨Cp, hCp0, hCp⟩ :=
    exists_finiteCoreSourceEnergy_uniform_reference_profile_bound hO hD g hg L K hK
  have hS : IsCompact (Icc (0 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod hK
  have hQex (a b : Fin 3) := exists_nonneg_norm_le_of_isCompact hS
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L a b).continuous
  have hbex (a : Fin 3) := exists_nonneg_norm_le_of_isCompact hS
    (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L a).continuous
  choose BQ hBQ0 hBQ using hQex
  choose Bb hBb0 hBb using hbex
  let P : ℝ := room.radiusJetBound
  have hP1 : 1 ≤ P := room.one_le_radiusJetBound
  have hP : 0 ≤ P := by linarith
  have hM : 0 ≤ M := by linarith
  have hMg : 0 ≤ Mg := by linarith
  let BQs : ℝ := ∑ a : Fin 3, ∑ b : Fin 3, BQ a b
  let Bbs : ℝ := ∑ a : Fin 3, Bb a
  have hBQs0 : 0 ≤ BQs := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hBQ0 a b
  have hBbs0 : 0 ≤ Bbs := Finset.sum_nonneg fun a _ => hBb0 a
  let c1 : ℝ := 9 * (BQs * (2 * (M * Mg)))
  let c2 : ℝ := 9 * (BQs * ufirstWordCoeff M Mg P Cc) +
    3 * (Bbs * (ufirstInclusionNorm * M))
  have hCUF : 0 ≤ 6 * (c1 ^ 2 + c2 ^ 2) * Cp :=
    mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (sq_nonneg c1) (sq_nonneg c2))) hCp0.le
  refine ⟨1 + 6 * (c1 ^ 2 + c2 ^ 2) * Cp, by linarith, ?_⟩
  intro q hq δ A hδ hδ1 hA p hp η hη hη1 BF hBF F0 y hy hBFβ hdR1 hroom
  have hp1 : 1 ≤ p := by omega
  let β : ℝ := actualReferenceBeta g L q δ A p y
  let r : ℝ := referenceRadius δ A p L y
  have hβ : 1 ≤ β := hBF.trans hBFβ
  have hβ0 : 0 ≤ β := by linarith
  -- actual caps at the point
  have hz := mem_correctionParameterSet (K := K) hq hy hdR1
  have hC0 : ∀ k, ‖referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y) k‖ ≤ M := fun k => (hMcap _ hz k).1
  have hC1 : ∀ k, ‖referenceNativeMovingAdjointParametricCorrection hF hO hD g L 1
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y) k‖ ≤ M := fun k => (hMcap _ hz k).2.1
  have hdC0 : ∀ k, ‖fderiv ℝ (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0 · k)
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y)‖ ≤ M := fun k => (hMcap _ hz k).2.2
  have hH : ‖fderiv ℝ (fderiv ℝ (referenceRadius δ A p L)) y‖ ≤ P :=
    norm_fderiv_fderiv_referenceRadius_le_bound room hq hδ hδ1 hA hp1 hη1 hy hroom
  obtain ⟨hfe0, -, -, hΓ0⟩ := hgeo q hq y hy
  have hfe : ∀ a k, ‖frameEntry g L a k (q,y)‖ ≤ Mg := fun a k => by
    rw [Real.norm_eq_abs]; exact hfe0 a k
  have hΓ : ∀ a b c, ‖referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) a) b c‖ ≤ Mg := fun a b c => by
    rw [Real.norm_eq_abs]; exact hΓ0 a b c
  have hf : ∀ a, ‖referenceRadiusHorizontalLogDerivative g L q (referenceRadius δ A p L) y a‖ ≤
      P * Cc * β := fun a => by
    rw [Real.norm_eq_abs]
    exact abs_horizontalLogDerivative_le g L q δ A p hδ hA y a P β Cc hP hβ0
      (norm_fderiv_referenceRadius_le room hq hδ hδ1 hA hp1 hy) (hCc q hq y hy a)
  have hQ : ∀ a b, ‖referenceDensityPrincipalFrameCoefficient g g2 L q y a b‖ ≤ BQs :=
    fun a b => (hBQ a b (q,y) ⟨hq, hy⟩).trans (le_sum_sum_fin_three BQ hBQ0 a b)
  have hb : ∀ a, ‖normalizedSecondDriftFrameJoint g g2 L a (q,y)‖ ≤ Bbs :=
    fun a => (hBb a (q,y) ⟨hq, hy⟩).trans
      (Finset.single_le_sum (f := Bb) (fun a' _ => hBb0 a') (Finset.mem_univ a))
  have hOut := norm_nativeUFirstOut_le hF hO hD g hg g2 L q δ A p hδ hA F0 y hM hMg hP hCc0 hβ
    hBQs0 hBbs0 hC0 hC1 hdC0 hH hfe hΓ hf hQ hb
  -- energy side
  let Hs : ℝ := ∑ k : Fin 3,
    ‖(coreDirectionalDerivative hO hD (coordinateDirection k) F0).val y‖
  let m : ℝ := ‖finiteCoreSobolevLift hO hD 1 F0 y‖
  have hHs0 : 0 ≤ Hs := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hm0 : 0 ≤ m := norm_nonneg _
  have hr0 : 0 ≤ r := (referenceRadius_pos δ A p L y hδ hA).le
  have hc1n : 0 ≤ c1 := mul_nonneg (by norm_num) (mul_nonneg hBQs0 (mul_nonneg (by norm_num)
    (mul_nonneg hM hMg)))
  have hH2 : Hs ^ 2 ≤ 3 * ∑ k : Fin 3,
      ‖(coreDirectionalDerivative hO hD (coordinateDirection k) F0).val y‖ ^ 2 :=
    sq_sum_fin_three_le _
  have hmE : m = ‖(coreWeightOperator hO hD (besselWeight 1) F0).val y‖ :=
    norm_finiteCoreSobolevLift hO hD 1 F0 y
  have hE := gradient_energy_le_finiteCoreSourceEnergy hO hD β hβ0 F0 y
  rw [← hmE] at hE
  have hSE := hCp q hq y hy β hβ F0
  have hPE := finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q β hβ0 F0 y
  let G2 : ℝ := ∑ k : Fin 3,
    ‖(coreDirectionalDerivative hO hD (coordinateDirection k) F0).val y‖ ^ 2
  have hG20 : 0 ≤ G2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  let X : ℝ := c1 * Hs + c2 * (β * m)
  have hsq : ‖nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0 y‖ ^ 2 ≤ (r * X) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hOut 2
  have hX2 : X ^ 2 ≤ 6 * (c1 ^ 2 + c2 ^ 2) * (G2 + β ^ 2 * m ^ 2) := by
    have e1 := mul_le_mul_of_nonneg_left hH2 (by positivity : (0:ℝ) ≤ 2 * c1 ^ 2)
    nlinarith [sq_nonneg (c1 * Hs - c2 * (β * m)), mul_nonneg (sq_nonneg c2) hG20,
      mul_nonneg (sq_nonneg c1) (mul_nonneg (sq_nonneg β) (sq_nonneg m))]
  have hX3 : X ^ 2 ≤ 6 * (c1 ^ 2 + c2 ^ 2) * Cp *
      finiteCoreReferenceProfileEnergy hO hD g hg L q β F0 y := by
    have h6 : (0:ℝ) ≤ 6 * (c1 ^ 2 + c2 ^ 2) := by positivity
    calc X ^ 2 ≤ 6 * (c1 ^ 2 + c2 ^ 2) * (G2 + β ^ 2 * m ^ 2) := hX2
      _ ≤ 6 * (c1 ^ 2 + c2 ^ 2) * (Cp * finiteCoreReferenceProfileEnergy hO hD g hg L q β F0 y) :=
          mul_le_mul_of_nonneg_left (hE.trans hSE) h6
      _ = _ := by ring
  exact ufirst_square_profile_finish hsq hX3 hPE

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
