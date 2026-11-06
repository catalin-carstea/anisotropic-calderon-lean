import Calderon.ActualPhysicalUFirstSmoothness
import Calderon.ActualRadiusThreeJetProfileRoom

/-! Author: Claude (Opus 5.5), v032. Expansion: output/MATHEMATICS.md, "Caps (expanded)".
Actual compact caps for `C_0`, `C_1`, `D C_0`, the conformal frame, the actual radius jets, `f_i`,
and the exact `I10` derivative commutation. No cap callback or new hypothesis. -/
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

open ReferenceWeightedApproximation

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevZeroEquiv
  sphereSobolevRotationL sphereSobolevShiftedDegreeL finiteCoreSobolevLift
  coreReferenceInput referenceNativeMovingAdjointParametricCorrection
  referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint
  referenceFrameConnectionCoefficient referenceMetricGramFrame referenceRadiusHorizontalLogDerivative
  nativeOneHorizontalAngularL nativeOneShiftedDegreeL nativeOneWeightedHorizontalAction
  nativeFirstCorrectionLift nativeUFirstWord nativeUFirstOut

-- actualSol: cache only the original canonical class data; do not replace norms or metrics.
@[instance_reducible] private def capsOriginalParameterNormed :
    NormedAddCommGroup ((ℝ × R3) × (R3 →L[ℝ] ℝ)) := inferInstance
@[instance_reducible] private def capsOriginalParameterModule :
    NormedSpace ℝ ((ℝ × R3) × (R3 →L[ℝ] ℝ)) := inferInstance
@[instance_reducible] private def capsOriginalCorrectionNormed :
    NormedAddCommGroup (SphereSobolev 0 →L[ℝ] SphereSobolev 0) := inferInstance
@[instance_reducible] private def capsOriginalCorrectionModule :
    NormedSpace ℝ (SphereSobolev 0 →L[ℝ] SphereSobolev 0) := inferInstance
@[instance_reducible] private def capsParameterNormed :
    NormedAddCommGroup ((ℝ × R3) × (R3 →L[ℝ] ℝ)) := capsOriginalParameterNormed
attribute [local instance] capsParameterNormed
@[instance_reducible] private def capsParameterModule :
    NormedSpace ℝ ((ℝ × R3) × (R3 →L[ℝ] ℝ)) := capsOriginalParameterModule
attribute [local instance] capsParameterModule
@[instance_reducible] private def capsCorrectionNormed :
    NormedAddCommGroup (SphereSobolev 0 →L[ℝ] SphereSobolev 0) := capsOriginalCorrectionNormed
attribute [local instance] capsCorrectionNormed
@[instance_reducible] private def capsCorrectionModule :
    NormedSpace ℝ (SphereSobolev 0 →L[ℝ] SphereSobolev 0) := capsOriginalCorrectionModule
attribute [local instance] capsCorrectionModule
private theorem capsParameterNormed_canonical : capsParameterNormed = capsOriginalParameterNormed := rfl
private theorem capsParameterModule_canonical : capsParameterModule = capsOriginalParameterModule := rfl
private theorem capsCorrectionNormed_canonical : capsCorrectionNormed = capsOriginalCorrectionNormed := rfl
private theorem capsCorrectionModule_canonical : capsCorrectionModule = capsOriginalCorrectionModule := rfl

/-! ### Compact parameter set -/

/-- `T = ([0,1] × K) × closedBall 0 1` in the parameter space of the actual correction. -/
def correctionParameterSet (K : Set R3) : Set ((ℝ × R3) × (R3 →L[ℝ] ℝ)) :=
  (Icc (0 : ℝ) 1 ×ˢ K) ×ˢ Metric.closedBall 0 1

lemma isCompact_correctionParameterSet (K : Set R3) (hK : IsCompact K) :
    IsCompact (correctionParameterSet K) :=
  (isCompact_Icc.prod hK).prod (isCompact_closedBall 0 1)

lemma mem_correctionParameterSet {K : Set R3} {q : ℝ} {y : R3} {d : R3 →L[ℝ] ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hy : y ∈ K) (hd : ‖d‖ ≤ 1) :
    (((q,y) : ℝ × R3), d) ∈ correctionParameterSet K :=
  ⟨⟨hq, hy⟩, mem_closedBall_zero_iff.mpr hd⟩

lemma exists_nonneg_norm_le_of_isCompact {X E : Type*} [TopologicalSpace X]
    [SeminormedAddCommGroup E] {S : Set X} (hS : IsCompact S) {f : X → E} (hf : Continuous f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ S, ‖f x‖ ≤ M := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩

/-! ### Correction caps -/

/-- One `M ≥ 1`, chosen from `K` and fixed data only, bounds `C_0`, `C_1` and `D C_0` on `T`. -/
theorem exists_correction_compact_caps (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (K : Set R3) (hK : IsCompact K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ z ∈ correctionParameterSet K, ∀ i : Fin 3,
      ‖referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0 z i‖ ≤ M ∧
      ‖referenceNativeMovingAdjointParametricCorrection hF hO hD g L 1 z i‖ ≤ M ∧
      ‖fderiv ℝ (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0 · i) z‖ ≤ M := by
  have hT := isCompact_correctionParameterSet K hK
  have hval (s : ℝ) (i : Fin 3) := exists_nonneg_norm_le_of_isCompact hT
    (contDiff_referenceNativeMovingAdjointParametricCorrection hF hO hD g hg L s i).continuous
  have hder (i : Fin 3) := exists_nonneg_norm_le_of_isCompact hT
    ((contDiff_referenceNativeMovingAdjointParametricCorrection hF hO hD g hg L 0 i).continuous_fderiv
      (by simp))
  choose A hA0 hA using hval
  choose B hB0 hB using hder
  have hterm (j : Fin 3) : 0 ≤ A 0 j + A 1 j + B j :=
    add_nonneg (add_nonneg (hA0 0 j) (hA0 1 j)) (hB0 j)
  have hsum (i : Fin 3) : A 0 i + A 1 i + B i ≤ ∑ j : Fin 3, (A 0 j + A 1 j + B j) :=
    Finset.single_le_sum (f := fun j => A 0 j + A 1 j + B j) (fun j _ => hterm j)
      (Finset.mem_univ i)
  have hnn : 0 ≤ ∑ j : Fin 3, (A 0 j + A 1 j + B j) := Finset.sum_nonneg (fun j _ => hterm j)
  refine ⟨1 + ∑ j : Fin 3, (A 0 j + A 1 j + B j), by linarith, fun z hz i => ⟨?_, ?_, ?_⟩⟩
  · have h1 := hA 0 i z hz
    have h2 := hsum i
    have h3 := hA0 1 i
    have h4 := hB0 i
    linarith
  · have h1 := hA 1 i z hz
    have h2 := hsum i
    have h3 := hA0 0 i
    have h4 := hB0 i
    linarith
  · have h1 := hB i z hz
    have h2 := hsum i
    have h3 := hA0 0 i
    have h4 := hA0 1 i
    linarith

/-- Actual conformal-frame cap on `[0,1] × K`. -/
theorem exists_conformalFrame_cap (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ K, ∀ i : Fin 3,
      ‖conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)‖ ≤ C := by
  have hS : IsCompact (Icc (0 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod hK
  have hb (i : Fin 3) := exists_nonneg_norm_le_of_isCompact hS
    ((contDiff_conformalReferenceGramFrameOperatorJoint g hg L).clm_apply
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × R3 => coordinateVector i))).continuous
  choose C hC0 hC using hb
  refine ⟨∑ j : Fin 3, C j, Finset.sum_nonneg (fun j _ => hC0 j), fun q hq y hy i => ?_⟩
  exact (hC i (q,y) ⟨hq, hy⟩).trans
    (Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_univ i))

/-! ### Actual radius jets -/

lemma norm_fderiv_referenceRadius_le {g : MatrixField} {L : ℝ} {K : Set R3}
    (room : ReferenceRadiusThreeJetProfileRoom g L K) {q δ A : ℝ} {p : ℕ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 < A) (hp : 1 ≤ p)
    {y : R3} (hy : y ∈ K) :
    ‖fderiv ℝ (referenceRadius δ A p L) y‖ ≤
      room.radiusJetBound * referenceRadius δ A p L y * actualReferenceBeta g L q δ A p y := by
  have h := room.radiusJets q hq δ hδ hδ1 A hA p hp y hy 1 (by norm_num)
  rwa [norm_iteratedFDeriv_one, pow_one] at h

lemma norm_fderiv_fderiv_referenceRadius_le {g : MatrixField} {L : ℝ} {K : Set R3}
    (room : ReferenceRadiusThreeJetProfileRoom g L K) {q δ A : ℝ} {p : ℕ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 < A) (hp : 1 ≤ p)
    {y : R3} (hy : y ∈ K) :
    ‖fderiv ℝ (fderiv ℝ (referenceRadius δ A p L)) y‖ ≤
      room.radiusJetBound * referenceRadius δ A p L y * actualReferenceBeta g L q δ A p y ^ 2 := by
  have h := room.radiusJets q hq δ hδ hδ1 A hA p hp y hy 2 (by norm_num)
  have e : ‖iteratedFDeriv ℝ 2 (referenceRadius δ A p L) y‖ =
      ‖fderiv ℝ (fderiv ℝ (referenceRadius δ A p L)) y‖ := by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ (referenceRadius δ A p L)),
      norm_iteratedFDeriv_fderiv]
  rwa [e] at h

/-- Under the profile room `r β² ≤ η ≤ 1`, the actual radius Hessian is bounded by `P`. -/
lemma norm_fderiv_fderiv_referenceRadius_le_bound {g : MatrixField} {L : ℝ} {K : Set R3}
    (room : ReferenceRadiusThreeJetProfileRoom g L K) {q δ A η : ℝ} {p : ℕ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 < A) (hp : 1 ≤ p)
    (hη1 : η ≤ 1) {y : R3} (hy : y ∈ K)
    (hroom : referenceRadius δ A p L y * actualReferenceBeta g L q δ A p y ^ 2 ≤ η) :
    ‖fderiv ℝ (fderiv ℝ (referenceRadius δ A p L)) y‖ ≤ room.radiusJetBound := by
  have h := norm_fderiv_fderiv_referenceRadius_le room hq hδ hδ1 hA hp hy
  have hP : 0 ≤ room.radiusJetBound := le_trans zero_le_one room.one_le_radiusJetBound
  have h2 : room.radiusJetBound * referenceRadius δ A p L y *
      actualReferenceBeta g L q δ A p y ^ 2 ≤ room.radiusJetBound * 1 := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hroom.trans hη1) hP
  linarith

/-- `|f_i| ≤ P·C·β` from `r f_i = dR(conf e_i)` and `r > 0`. -/
lemma abs_horizontalLogDerivative_le (g : MatrixField) (L q δ A : ℝ) (p : ℕ) (hδ : 0 < δ)
    (hA : 0 < A) (y : R3) (i : Fin 3) (P β C : ℝ) (hP : 0 ≤ P) (hβ : 0 ≤ β)
    (hdR : ‖fderiv ℝ (referenceRadius δ A p L) y‖ ≤ P * referenceRadius δ A p L y * β)
    (hconf : ‖conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)‖ ≤ C) :
    |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δ A p L) y i| ≤ P * C * β := by
  have hR : ContDiff ℝ ∞ (referenceRadius δ A p L) :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ A p L hδ hA
  have hr : 0 < referenceRadius δ A p L y := referenceRadius_pos δ A p L y hδ hA
  have hid := referenceRadius_mul_horizontalLogDerivative_eq_fderiv g L q
    (referenceRadius δ A p L) hR y hr.ne' i
  have h2 : |referenceRadius δ A p L y *
      referenceRadiusHorizontalLogDerivative g L q (referenceRadius δ A p L) y i| ≤
      referenceRadius δ A p L y * (P * C * β) := by
    rw [hid, ← Real.norm_eq_abs]
    calc _ ≤ ‖fderiv ℝ (referenceRadius δ A p L) y‖ *
          ‖conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (P * referenceRadius δ A p L y * β) * C :=
          mul_le_mul hdR hconf (norm_nonneg _) (mul_nonneg (mul_nonneg hP hr.le) hβ)
      _ = referenceRadius δ A p L y * (P * C * β) := by ring
  rw [abs_mul, abs_of_pos hr] at h2
  exact le_of_mul_le_mul_left h2 hr

/-! ### I10 commutes through the derivative of the first correction (v031 §2, I1–I2) -/

/-- (I1) `I10 (V_j x) = C_0(z x) j (Z (F0 x))`: no `H^1` norm of a base derivative. -/
lemma inclusion_nativeFirstCorrectionLift_eq (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField) (L q : ℝ)
    (R : R3 → ℝ) (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) (x : R3) :
    sphereSobolevInclusionL 1 0 (by norm_num) (nativeFirstCorrectionLift hF hO hD g L q R F0 j x) =
      referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0 ((q,x),fderiv ℝ R x) j
        (sphereSobolevZeroEquiv hO hD (F0.val x)) := by
  have hRep : sphereSobolevInclusionL 1 0 (by norm_num) (finiteCoreSobolevLift hO hD 1 F0 x) =
      sphereSobolevZeroEquiv hO hD (F0.val x) :=
    (finiteCoreSobolevLift_representation hO hD 1 (by norm_num) F0).2.2.2.1 x
  unfold nativeFirstCorrectionLift
  have hCompat := referenceNativeMovingAdjointParametricCorrection_inclusion hF hO hD g L 1 0
    (by norm_num) ((q,x),fderiv ℝ R x) j (finiteCoreSobolevLift hO hD 1 F0 x)
  exact hCompat.trans
    (congrArg (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
      ((q,x),fderiv ℝ R x) j) hRep)

/-- (I2) `I10 (dV_j(y) v) = d(x ↦ C_0(z x) j (Z (F0 x)))(y) v`. -/
lemma inclusion_fderiv_nativeFirstCorrectionLift_eq (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) (y v : R3) :
    sphereSobolevInclusionL 1 0 (by norm_num)
        (fderiv ℝ (nativeFirstCorrectionLift hF hO hD g L q R F0 j) y v) =
      fderiv ℝ (fun x => referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
        ((q,x),fderiv ℝ R x) j (sphereSobolevZeroEquiv hO hD (F0.val x))) y v := by
  have hV := contDiff_nativeFirstCorrectionLift hF hO hD g hg L q R hR F0 j
  have hcomp : fderiv ℝ (fun x => sphereSobolevInclusionL 1 0 (by norm_num)
        (nativeFirstCorrectionLift hF hO hD g L q R F0 j x)) y =
      (sphereSobolevInclusionL 1 0 (by norm_num)).comp
        (fderiv ℝ (nativeFirstCorrectionLift hF hO hD g L q R F0 j) y) :=
    ((sphereSobolevInclusionL 1 0 (by norm_num)).hasFDerivAt.comp y
      ((hV.differentiable (by simp)) y).hasFDerivAt).fderiv
  have hfun : (fun x => sphereSobolevInclusionL 1 0 (by norm_num)
        (nativeFirstCorrectionLift hF hO hD g L q R F0 j x)) =
      (fun x => referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
        ((q,x),fderiv ℝ R x) j (sphereSobolevZeroEquiv hO hD (F0.val x))) :=
    funext (fun x => inclusion_nativeFirstCorrectionLift_eq hF hO hD g L q R F0 j x)
  have hValue : sphereSobolevInclusionL 1 0 (by norm_num)
      (fderiv ℝ (nativeFirstCorrectionLift hF hO hD g L q R F0 j) y v) =
      fderiv ℝ (fun x => sphereSobolevInclusionL 1 0 (by norm_num)
        (nativeFirstCorrectionLift hF hO hD g L q R F0 j x)) y v :=
    (congrArg (fun T : R3 →L[ℝ] SphereSobolev 0 => T v) hcomp).symm
  exact hValue.trans (congrArg (fun F : R3 → SphereSobolev 0 => fderiv ℝ F y v) hfun)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
