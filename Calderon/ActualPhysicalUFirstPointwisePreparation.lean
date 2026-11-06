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

/-! ### Fixed operator-norm constants -/

/-- `cI = ‖I_{1→0}‖`. -/
def ufirstInclusionNorm : ℝ := ‖sphereSobolevInclusionL 1 0 (by norm_num : (0 : ℝ) ≤ 1)‖

/-- `cA = ‖I_{0→0}‖ · Σ_ab ‖Rot^1_ab‖` (the angular connection is `≤ Mg · cA`). -/
def ufirstAngularNorm : ℝ :=
  ‖sphereSobolevInclusionL ((1:ℝ)-1) 0 (by norm_num)‖ *
    ∑ a : Fin 3, ∑ b : Fin 3, ‖sphereSobolevRotationL 1 a b‖

/-- `cDeg = ‖nativeOneShiftedDegreeL‖`. -/
def ufirstDegreeNorm : ℝ := ‖nativeOneShiftedDegreeL‖

/-- `Ce = Σ_k ‖e_k‖`. -/
def ufirstDirectionNorm : ℝ := ∑ k : Fin 3, ‖coordinateDirection k‖

lemma ufirstInclusionNorm_nonneg : 0 ≤ ufirstInclusionNorm := norm_nonneg _

lemma ufirstAngularNorm_nonneg : 0 ≤ ufirstAngularNorm :=
  mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)

lemma ufirstDegreeNorm_nonneg : 0 ≤ ufirstDegreeNorm := norm_nonneg _

lemma ufirstDirectionNorm_nonneg : 0 ≤ ufirstDirectionNorm :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Coefficient of `β m` in the word bound (MATHEMATICS.md, "Six words"). -/
def ufirstWordCoeff (M Mg P Cc : ℝ) : ℝ :=
  M * (1 + P) * (Mg * ufirstDirectionNorm) * ufirstInclusionNorm +
    2 * (M * Mg * ufirstAngularNorm) + 3 * (Mg * ufirstInclusionNorm * M) +
    M * ufirstInclusionNorm * M + 2 * (P * Cc * ufirstDegreeNorm * M)

/-! ### Elementary finite estimates -/

lemma norm_add_add_add_sub_add_le {E : Type*} [SeminormedAddCommGroup E] (a b c d e f : E) :
    ‖a + b + c + d - e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have h1 := norm_add_le (a + b + c + d - e) f
  have h2 := norm_sub_le (a + b + c + d) e
  have h3 := norm_add_le (a + b + c) d
  have h4 := norm_add_le (a + b) c
  have h5 := norm_add_le a b
  linarith

lemma norm_add_add_le' {E : Type*} [SeminormedAddCommGroup E] (a b c : E) :
    ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h1 := norm_add_le (a + b) c
  have h2 := norm_add_le a b
  linarith

lemma sq_sum_fin_three_le (h : Fin 3 → ℝ) : (∑ k, h k) ^ 2 ≤ 3 * ∑ k, h k ^ 2 := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (h 0 - h 1), sq_nonneg (h 1 - h 2), sq_nonneg (h 0 - h 2)]

lemma le_sum_sum_fin_three (B : Fin 3 → Fin 3 → ℝ) (hB : ∀ a b, 0 ≤ B a b) (a b : Fin 3) :
    B a b ≤ ∑ a' : Fin 3, ∑ b' : Fin 3, B a' b' :=
  (Finset.single_le_sum (f := fun b' => B a b') (fun b' _ => hB a b') (Finset.mem_univ b)).trans
    (Finset.single_le_sum (f := fun a' => ∑ b' : Fin 3, B a' b')
      (fun a' _ => Finset.sum_nonneg fun b' _ => hB a' b') (Finset.mem_univ a))

lemma norm_half_smul_double_sum_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : Fin 3 → Fin 3 → ℝ)
    (T : Fin 3 → Fin 3 → E →L[ℝ] F) {Mg : ℝ} (hc : ∀ a b, ‖c a b‖ ≤ Mg) :
    ‖(1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, c a b • T a b‖ ≤
      Mg * ∑ a : Fin 3, ∑ b : Fin 3, ‖T a b‖ := by
  have hS : ‖∑ a : Fin 3, ∑ b : Fin 3, c a b • T a b‖ ≤
      Mg * ∑ a : Fin 3, ∑ b : Fin 3, ‖T a b‖ := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hc a b) (norm_nonneg _)
  have hh : ‖(1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, c a b • T a b‖ =
      (1/2) * ‖∑ a : Fin 3, ∑ b : Fin 3, c a b • T a b‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  rw [hh]
  have h0 := norm_nonneg (∑ a : Fin 3, ∑ b : Fin 3, c a b • T a b)
  linarith

/-! ### I3: chain/product estimate -/

/-- Generic product rule estimate `D(Φ∘z · w)`. -/
theorem norm_fderiv_clm_apply_comp_le {E X G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Φ : X → G →L[ℝ] H) (z : E → X) (w : E → G) (y v : E)
    (hΦ : DifferentiableAt ℝ Φ (z y)) (hz : DifferentiableAt ℝ z y)
    (hw : DifferentiableAt ℝ w y) {M Pz : ℝ} (hM : 0 ≤ M) (hPz : 0 ≤ Pz)
    (hΦy : ‖Φ (z y)‖ ≤ M) (hdΦ : ‖fderiv ℝ Φ (z y)‖ ≤ M) (hdz : ‖fderiv ℝ z y‖ ≤ Pz) :
    ‖fderiv ℝ (fun x => Φ (z x) (w x)) y v‖ ≤
      M * ‖fderiv ℝ w y v‖ + M * Pz * ‖v‖ * ‖w y‖ := by
  have hC : HasFDerivAt (fun x => Φ (z x)) ((fderiv ℝ Φ (z y)).comp (fderiv ℝ z y)) y :=
    hΦ.hasFDerivAt.comp y hz.hasFDerivAt
  have h : fderiv ℝ (fun x => Φ (z x) (w x)) y =
      (Φ (z y)).comp (fderiv ℝ w y) +
        ((fderiv ℝ Φ (z y)).comp (fderiv ℝ z y)).flip (w y) :=
    (hC.clm_apply hw.hasFDerivAt).fderiv
  rw [h, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply]
  have h1 : ‖Φ (z y) (fderiv ℝ w y v)‖ ≤ M * ‖fderiv ℝ w y v‖ :=
    (Φ (z y)).le_of_opNorm_le hΦy _
  have hzv : ‖fderiv ℝ z y v‖ ≤ Pz * ‖v‖ := (fderiv ℝ z y).le_of_opNorm_le hdz v
  have h2 : ‖(fderiv ℝ Φ (z y) (fderiv ℝ z y v)) (w y)‖ ≤ M * Pz * ‖v‖ * ‖w y‖ := by
    refine ((fderiv ℝ Φ (z y) (fderiv ℝ z y v)).le_opNorm (w y)).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖fderiv ℝ Φ (z y) (fderiv ℝ z y v)‖ ≤ M * ‖fderiv ℝ z y v‖ :=
          (fderiv ℝ Φ (z y)).le_of_opNorm_le hdΦ _
      _ ≤ M * (Pz * ‖v‖) := mul_le_mul_of_nonneg_left hzv hM
      _ = M * Pz * ‖v‖ := by ring
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- `‖D(x ↦ ((q,x), dR x))(y)‖ ≤ 1 + P` when `‖D²R(y)‖ ≤ P`. -/
lemma norm_fderiv_correctionParameter_le (q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (y : R3)
    {P : ℝ} (hP : 0 ≤ P) (hH : ‖fderiv ℝ (fderiv ℝ R) y‖ ≤ P) :
    ‖fderiv ℝ (fun x : R3 => (((q,x) : ℝ × R3), fderiv ℝ R x)) y‖ ≤ 1 + P := by
  have hR2 : Differentiable ℝ (fderiv ℝ R) :=
    (contDiff_infty_iff_fderiv.mp hR).2.differentiable (by simp)
  have hz : HasFDerivAt (fun x : R3 => (((q,x) : ℝ × R3), fderiv ℝ R x))
      (((0 : R3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ R3)).prod
        (fderiv ℝ (fderiv ℝ R) y)) y :=
    ((hasFDerivAt_const q y).prodMk (hasFDerivAt_id y)).prodMk (hR2 y).hasFDerivAt
  rw [hz.fderiv]
  simp only [ContinuousLinearMap.opNorm_prod, Prod.norm_mk, norm_zero]
  exact max_le (max_le (by linarith)
    ((ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := R3)).trans (by linarith)))
    (hH.trans (by linarith))

/-- (I3) `‖I10(dV_j(y)v)‖ ≤ M‖I10(dW(y)v)‖ + M(1+P)‖v‖‖I10(W y)‖`, after commuting `I10`
through the derivative by the saved (I2). -/
theorem norm_inclusion_fderiv_nativeFirstCorrectionLift_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) (y v : R3) {M P : ℝ}
    (hM : 0 ≤ M) (hP : 0 ≤ P)
    (hC0 : ‖referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
      ((q,y),fderiv ℝ R y) j‖ ≤ M)
    (hdC0 : ‖fderiv ℝ (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0 · j)
      ((q,y),fderiv ℝ R y)‖ ≤ M)
    (hH : ‖fderiv ℝ (fderiv ℝ R) y‖ ≤ P) :
    ‖sphereSobolevInclusionL 1 0 (by norm_num)
        (fderiv ℝ (nativeFirstCorrectionLift hF hO hD g L q R F0 j) y v)‖ ≤
      M * ‖sphereSobolevInclusionL 1 0 (by norm_num)
          (fderiv ℝ (finiteCoreSobolevLift hO hD 1 F0) y v)‖ +
        M * (1 + P) * ‖v‖ *
          ‖sphereSobolevInclusionL 1 0 (by norm_num) (finiteCoreSobolevLift hO hD 1 F0 y)‖ := by
  have hWd : DifferentiableAt ℝ (finiteCoreSobolevLift hO hD 1 F0) y :=
    (contDiff_finiteCoreSobolevLift hO hD 1 F0).differentiable (by simp) y
  have hfun : (fun x => referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
        ((q,x),fderiv ℝ R x) j (sphereSobolevZeroEquiv hO hD (F0.val x))) =
      (fun x => referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
        ((q,x),fderiv ℝ R x) j (sphereSobolevInclusionL 1 0 (by norm_num)
          (finiteCoreSobolevLift hO hD 1 F0 x))) :=
    funext fun x => by
      rw [(finiteCoreSobolevLift_representation hO hD 1 (by norm_num) F0).2.2.2.1 x]
  have hw : fderiv ℝ (fun x => sphereSobolevInclusionL 1 0 (by norm_num)
        (finiteCoreSobolevLift hO hD 1 F0 x)) y =
      (sphereSobolevInclusionL 1 0 (by norm_num)).comp
        (fderiv ℝ (finiteCoreSobolevLift hO hD 1 F0) y) :=
    ((sphereSobolevInclusionL 1 0 (by norm_num)).hasFDerivAt.comp y hWd.hasFDerivAt).fderiv
  have hz : DifferentiableAt ℝ (fun x : R3 => (((q,x) : ℝ × R3), fderiv ℝ R x)) y :=
    ((differentiableAt_const q).prodMk differentiableAt_id).prodMk
      (((contDiff_infty_iff_fderiv.mp hR).2.differentiable (by simp)) y)
  have hΦ : DifferentiableAt ℝ
      (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0 · j)
      ((q,y),fderiv ℝ R y) :=
    (contDiff_referenceNativeMovingAdjointParametricCorrection hF hO hD g hg L 0 j).differentiable
      (by simp) _
  have h := norm_fderiv_clm_apply_comp_le
    (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0 · j)
    (fun x : R3 => (((q,x) : ℝ × R3), fderiv ℝ R x))
    (fun x => sphereSobolevInclusionL 1 0 (by norm_num) (finiteCoreSobolevLift hO hD 1 F0 x))
    y v hΦ hz ((sphereSobolevInclusionL 1 0 (by norm_num)).differentiableAt.comp y hWd)
    hM (by linarith) hC0 hdC0 (norm_fderiv_correctionParameter_le q R hR y hP hH)
  have hwv : fderiv ℝ (fun x => sphereSobolevInclusionL 1 0 (by norm_num)
        (finiteCoreSobolevLift hO hD 1 F0 x)) y v =
      sphereSobolevInclusionL 1 0 (by norm_num)
        (fderiv ℝ (finiteCoreSobolevLift hO hD 1 F0) y v) :=
    congrArg (fun T : R3 →L[ℝ] SphereSobolev 0 => T v) hw
  have hRight := congrArg (fun a : ℝ => M * a + M * (1 + P) * ‖v‖ *
      ‖sphereSobolevInclusionL 1 0 (by norm_num) (finiteCoreSobolevLift hO hD 1 F0 y)‖)
    (congrArg (fun t : SphereSobolev 0 => ‖t‖) hwv)
  have hBound := h.trans_eq hRight
  have hFunctionDerivative := congrArg
    (fun f : R3 → SphereSobolev 0 => fderiv ℝ f y v) hfun
  have hLeft := (inclusion_fderiv_nativeFirstCorrectionLift_eq hF hO hD g hg L q R hR F0 j y v).trans
    hFunctionDerivative
  exact (congrArg (fun t : SphereSobolev 0 => ‖t‖) hLeft).le.trans hBound

/-! ### I4: frame and finite coordinate derivatives -/

lemma norm_clm_apply_referenceMetricGramFrame_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3) (D : R3 →L[ℝ] E)
    {Mg : ℝ} (hfe : ∀ k, ‖frameEntry g L i k (q,y)‖ ≤ Mg) :
    ‖D (referenceMetricGramFrame g L (q,y) i)‖ ≤ Mg * ∑ k : Fin 3, ‖D (coordinateDirection k)‖ := by
  rw [referenceGramFrame_eq_sum_coordinateDirection g L q y i, map_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [map_smul, norm_smul]
  exact mul_le_mul_of_nonneg_right (hfe k) (norm_nonneg _)

lemma norm_referenceMetricGramFrame_le (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3)
    {Mg : ℝ} (hfe : ∀ k, ‖frameEntry g L i k (q,y)‖ ≤ Mg) :
    ‖referenceMetricGramFrame g L (q,y) i‖ ≤ Mg * ufirstDirectionNorm := by
  have h := norm_clm_apply_referenceMetricGramFrame_le g L q y i
    (ContinuousLinearMap.id ℝ R3) hfe
  simpa only [ContinuousLinearMap.id_apply, ufirstDirectionNorm] using h

/-- (I4) `‖I10(dW(y)e_k)‖ = ‖(∂_{e_k} F0).val y‖`. -/
lemma norm_inclusion_fderiv_finiteCoreSobolevLift_coordinate
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) (k : Fin 3) :
    ‖sphereSobolevInclusionL 1 0 (by norm_num)
        (fderiv ℝ (finiteCoreSobolevLift hO hD 1 F0) y (coordinateDirection k))‖ =
      ‖(coreDirectionalDerivative hO hD (coordinateDirection k) F0).val y‖ := by
  have hd : fderiv ℝ (finiteCoreSobolevLift hO hD 1 F0) y (coordinateDirection k) =
      finiteCoreSobolevLift hO hD 1 (coreDirectionalDerivative hO hD (coordinateDirection k) F0) y :=
    directionalFDeriv_finiteCoreSobolevLift hO hD 1 F0 (coordinateDirection k) y
  rw [hd, (finiteCoreSobolevLift_representation hO hD 1 (by norm_num)
    (coreDirectionalDerivative hO hD (coordinateDirection k) F0)).2.2.2.1 y]
  exact (sphereSobolevZeroEquiv hO hD).norm_map _

/-- (I4) `‖I10(dW(y)X_i)‖ ≤ Mg Σ_k h_k`. -/
lemma norm_inclusion_fderiv_finiteCoreSobolevLift_frame_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField) (L q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) (i : Fin 3) {Mg : ℝ}
    (hfe : ∀ k, ‖frameEntry g L i k (q,y)‖ ≤ Mg) :
    ‖sphereSobolevInclusionL 1 0 (by norm_num)
        (fderiv ℝ (finiteCoreSobolevLift hO hD 1 F0) y (referenceMetricGramFrame g L (q,y) i))‖ ≤
      Mg * ∑ k : Fin 3, ‖(coreDirectionalDerivative hO hD (coordinateDirection k) F0).val y‖ := by
  have h := norm_clm_apply_referenceMetricGramFrame_le g L q y i
    ((sphereSobolevInclusionL 1 0 (by norm_num)).comp
      (fderiv ℝ (finiteCoreSobolevLift hO hD 1 F0) y)) hfe
  simp only [ContinuousLinearMap.comp_apply,
    norm_inclusion_fderiv_finiteCoreSobolevLift_coordinate] at h
  exact h

/-! ### I5: actual weighted core input formula (graph route) -/

theorem zeroEquiv_coreReferenceInput_eq (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g) (L q δ A : ℝ)
    (p : ℕ) (hδ : 0 < δ) (hA : 0 < A) (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3)
    (j : Fin 3) :
    sphereSobolevZeroEquiv hO hD ((coreReferenceInput hO hD g hg L q δ A p j hδ hA F0).val y) =
      nativeOneWeightedHorizontalAction g L q (referenceRadius δ A p L)
        (finiteCoreSobolevLift hO hD 1 F0) y j := by
  apply sphereSobolevInclusionL_injective 0 (-(1/2 : ℝ)) (by norm_num)
  rw [sphereSobolevInclusionL_nativeOneWeightedHorizontalAction g L q _ _ y j
    ((contDiff_finiteCoreSobolevLift hO hD 1 F0).differentiable (by simp) y)]
  have hfun : (fun x => sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num)
      (finiteCoreSobolevLift hO hD 1 F0 x)) = finiteCoreSobolevLift hO hD (1/2 : ℝ) F0 :=
    funext fun x => sphereSobolevInclusionL_finiteCoreSobolevLift hO hD 1 (1/2 : ℝ)
      (by norm_num) F0 x
  rw [hfun, ← finiteCoreSobolevLift_negative_half_eq_zero_inclusion hO hD _ y]
  exact (referenceLowerWeightedHorizontalAction_finiteCoreSobolevLift hO hD g hg L q δ A p
    hδ hA F0 y j).symm

/-- (I5, unfolded) `Z(core_j y) = I10(dW(y)X_j) + Ang_j(W y) + f_j • Deg(W y)`. -/
theorem zeroEquiv_coreReferenceInput_eq_expanded (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g) (L q δ A : ℝ)
    (p : ℕ) (hδ : 0 < δ) (hA : 0 < A) (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3)
    (j : Fin 3) :
    sphereSobolevZeroEquiv hO hD ((coreReferenceInput hO hD g hg L q δ A p j hδ hA F0).val y) =
      sphereSobolevInclusionL 1 0 (by norm_num)
          (fderiv ℝ (finiteCoreSobolevLift hO hD 1 F0) y (referenceMetricGramFrame g L (q,y) j)) +
        nativeOneHorizontalAngularL g L q y j (finiteCoreSobolevLift hO hD 1 F0 y) +
        referenceRadiusHorizontalLogDerivative g L q (referenceRadius δ A p L) y j •
          nativeOneShiftedDegreeL (finiteCoreSobolevLift hO hD 1 F0 y) :=
  by
    simpa only [nativeOneWeightedHorizontalAction] using
      (zeroEquiv_coreReferenceInput_eq hO hD g hg L q δ A p hδ hA F0 y j)

/-! ### Angular connection operator norm -/

lemma norm_nativeOneHorizontalAngularL_le (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3)
    {Mg : ℝ} (hΓ : ∀ a b, ‖referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) a b‖ ≤ Mg) :
    ‖nativeOneHorizontalAngularL g L q y i‖ ≤ Mg * ufirstAngularNorm := by
  unfold nativeOneHorizontalAngularL ufirstAngularNorm
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h := norm_half_smul_double_sum_le
    (fun a b => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) a b)
    (fun a b => sphereSobolevRotationL 1 a b) hΓ
  calc _ ≤ ‖sphereSobolevInclusionL ((1:ℝ)-1) 0 (by norm_num)‖ *
        (Mg * ∑ a : Fin 3, ∑ b : Fin 3, ‖sphereSobolevRotationL 1 a b‖) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by ring


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_inclusion_fderiv_nativeFirstCorrectionLift_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.zeroEquiv_coreReferenceInput_eq
