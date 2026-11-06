import Calderon.ActualFinitePhysicalModelFullErrorDictionary
import Calderon.ActualNativeMovingAdjointCorrectionInclusion
import Calderon.ActualNativeMovingAdjointFiniteJ
import Calderon.ActualWeightedHorizontalActions
import Calderon.SphereSobolevShiftedPhysicalDegree
import Calderon.SphereSobolevZeroEquivIdentities
import Calderon.ActualFiniteCoreSobolevRepresentation
import Calderon.ActualNativePhysicalModelInputDictionary

/-! Author: Claude (Opus 5.5). Expansion: output/MATHEMATICS.md, Sections 1-2.
Actual native H0 output of the literal first-correction word `UFirst` of
`referencePhysicalDensityOperator_finiteCore_eq_nativeModel_add_full_residual`,
its exact negative graph, and support control. No quantitative claim here. -/
set_option autoImplicit false
noncomputable section
open Set Filter
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
  PrincipalCommutator BoundedAngularShift

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevZeroEquiv
  sphereSobolevRotationL sphereSobolevShiftedDegreeL
  finiteCoreSobolevLift coreReferenceInput referenceNativeMovingAdjointParametricCorrection
  referenceHighWeightedHorizontalAction referenceLowerWeightedHorizontalAction
  referenceHighHorizontalAction referenceLowerHorizontalAction
  sphereSobolevRadialDriftAdjointL sphereSobolevLinearCoordinateMulL
  referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint
  referenceFrameConnectionCoefficient referenceMetricGramFrame referenceRadiusHorizontalLogDerivative

/-! ### Coefficient compatibilities -/

lemma sphereSobolevInclusionL_comp_inclusionL_apply (s t r : ℝ) (hts : t ≤ s) (hrt : r ≤ t)
    (u : SphereSobolev s) :
    sphereSobolevInclusionL t r hrt (sphereSobolevInclusionL s t hts u) =
      sphereSobolevInclusionL s r (hrt.trans hts) u := by
  apply sphereSobolev_ext r
  intro k
  rw [sphereSobolevCoefficientL_inclusion, sphereSobolevCoefficientL_inclusion,
    sphereSobolevCoefficientL_inclusion]

lemma sphereSobolevCoefficientL_negHalf_eq_half_sub_one (k : ℕ) :
    (sphereSobolevCoefficientL (-(1/2 : ℝ)) k :
      SphereSobolev (-(1/2 : ℝ)) →L[ℝ] harmonicSphereSubspace k) =
      sphereSobolevCoefficientL ((1/2 : ℝ)-1) k := by
  change sphereSobolevCoefficientL (-(1/2 : ℝ)) k =
    sphereSobolevCoefficientL ((1/2 : ℝ)-1) k
  rw [show (1/2 : ℝ)-1 = (-(1/2 : ℝ)) by norm_num]

/-- Order-one shifted degree, read in `H^{-1/2}`, is the half-order shifted degree. -/
lemma sphereSobolevInclusionL_shiftedDegree_one (w : SphereSobolev 1) :
    sphereSobolevInclusionL ((1:ℝ)-1) (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevShiftedDegreeL 1 w) =
    sphereSobolevShiftedDegreeL (1/2 : ℝ) (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) w) := by
  apply sphereSobolev_ext (-(1/2 : ℝ))
  intro k
  have hL1 := sphereSobolevCoefficientL_inclusion ((1:ℝ)-1) (-(1/2 : ℝ)) (by norm_num)
    (sphereSobolevShiftedDegreeL 1 w) k
  have hL2 := sphereSobolevCoefficientL_shiftedDegree 1 k w
  have hR1 := congrArg
    (fun T : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] harmonicSphereSubspace k =>
      T (sphereSobolevShiftedDegreeL (1/2 : ℝ)
        (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) w)))
    (sphereSobolevCoefficientL_negHalf_eq_half_sub_one k)
  have hR2 := sphereSobolevCoefficientL_shiftedDegree (1/2 : ℝ) k
    (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) w)
  have hR3 := sphereSobolevCoefficientL_inclusion 1 (1/2 : ℝ) (by norm_num) w k
  exact hL1.trans (hL2.trans ((congrArg (fun v : harmonicSphereSubspace k => (k : ℝ) • v)
    hR3.symm).trans (hR2.symm.trans hR1.symm)))

/-- Order-one rotation, read in `H^{-1/2}`, is the half-order rotation. -/
lemma sphereSobolevInclusionL_rotation_one (a b : Fin 3) (w : SphereSobolev 1) :
    sphereSobolevInclusionL ((1:ℝ)-1) (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevRotationL 1 a b w) =
    sphereSobolevRotationL (1/2 : ℝ) a b (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) w) := by
  apply sphereSobolev_ext (-(1/2 : ℝ))
  intro k
  have hL1 := sphereSobolevCoefficientL_inclusion ((1:ℝ)-1) (-(1/2 : ℝ)) (by norm_num)
    (sphereSobolevRotationL 1 a b w) k
  have hL2 := sphereSobolevCoefficientL_rotation 1 a b k w
  have hR1 := congrArg
    (fun T : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] harmonicSphereSubspace k =>
      T (sphereSobolevRotationL (1/2 : ℝ) a b
        (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) w)))
    (sphereSobolevCoefficientL_negHalf_eq_half_sub_one k)
  have hR2 := sphereSobolevCoefficientL_rotation (1/2 : ℝ) a b k
    (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) w)
  have hR3 := sphereSobolevCoefficientL_inclusion 1 (1/2 : ℝ) (by norm_num) w k
  exact hL1.trans (hL2.trans ((congrArg (harmonicSphereRotation k a b) hR3.symm).trans
    (hR2.symm.trans hR1.symm)))

/-! ### Native order-one angular connection, degree and weighted action -/

/-- Original angular connection `½ Σ Γ_ab Rotation_ab` with source `H^1`, target `H^0`. -/
def nativeOneHorizontalAngularL (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (sphereSobolevInclusionL ((1:ℝ)-1) 0 (by norm_num)).comp
    ((1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
      referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) a b •
        sphereSobolevRotationL 1 a b)

/-- Original shifted physical degree (eigenvalue `k`) with source `H^1`, target `H^0`. -/
def nativeOneShiftedDegreeL : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (sphereSobolevInclusionL ((1:ℝ)-1) 0 (by norm_num)).comp (sphereSobolevShiftedDegreeL 1)

/-- Native weighted horizontal action: derivative + angular connection PLUS `f_i • degree`. -/
def nativeOneWeightedHorizontalAction (g : MatrixField) (L q : ℝ) (R : R3 → ℝ)
    (V : R3 → SphereSobolev 1) (y : R3) (i : Fin 3) : SphereSobolev 0 :=
  sphereSobolevInclusionL 1 0 (by norm_num) (fderiv ℝ V y (referenceMetricGramFrame g L (q,y) i)) +
    nativeOneHorizontalAngularL g L q y i (V y) +
    referenceRadiusHorizontalLogDerivative g L q R y i • nativeOneShiftedDegreeL (V y)

attribute [local irreducible] nativeOneHorizontalAngularL nativeOneShiftedDegreeL
  nativeOneWeightedHorizontalAction

lemma sphereSobolevInclusionL_nativeOneHorizontalAngularL
    (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3) (w : SphereSobolev 1) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (nativeOneHorizontalAngularL g L q y i w) =
      referenceLowerHorizontalAngularL g L q y i
        (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) w) := by
  simp only [nativeOneHorizontalAngularL, referenceLowerHorizontalAngularL,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, map_smul, map_sum,
    sphereSobolevInclusionL_comp_inclusionL_apply, sphereSobolevInclusionL_rotation_one]

lemma sphereSobolevInclusionL_nativeOneShiftedDegreeL (w : SphereSobolev 1) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (nativeOneShiftedDegreeL w) =
      sphereSobolevShiftedDegreeL (1/2 : ℝ) (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) w) := by
  simp only [nativeOneShiftedDegreeL, ContinuousLinearMap.comp_apply,
    sphereSobolevInclusionL_comp_inclusionL_apply, sphereSobolevInclusionL_shiftedDegree_one]

/-- Graph of the native weighted action: it is the original lower weighted action of the
`H^{1/2}` inclusion of the field (same frame, connection, PLUS `f_i • shiftedDegree`). -/
lemma sphereSobolevInclusionL_nativeOneWeightedHorizontalAction
    (g : MatrixField) (L q : ℝ) (R : R3 → ℝ) (V : R3 → SphereSobolev 1) (y : R3) (i : Fin 3)
    (hV : DifferentiableAt ℝ V y) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (nativeOneWeightedHorizontalAction g L q R V y i) =
    referenceLowerWeightedHorizontalAction g L q R
      (fun x => sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) (V x)) y i := by
  have hDeriv : fderiv ℝ (fun x => sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) (V x)) y =
      (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num)).comp (fderiv ℝ V y) :=
    ((sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num)).hasFDerivAt.comp y hV.hasFDerivAt).fderiv
  simp only [nativeOneWeightedHorizontalAction, referenceLowerWeightedHorizontalAction,
    referenceLowerHorizontalAction, hDeriv, ContinuousLinearMap.comp_apply, map_add, map_smul,
    sphereSobolevInclusionL_comp_inclusionL_apply,
    sphereSobolevInclusionL_nativeOneHorizontalAngularL,
    sphereSobolevInclusionL_nativeOneShiftedDegreeL]

/-! ### The actual first-correction field and the native UFirst output -/

/-- Compatible `H^1` lift `C^1_j(z x)(u_1 x)` of the actual first correction field. -/
def nativeFirstCorrectionLift (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L q : ℝ) (R : R3 → ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) (x : R3) : SphereSobolev 1 :=
  referenceNativeMovingAdjointParametricCorrection hF hO hD g L 1 ((q,x),fderiv ℝ R x) j
    (finiteCoreSobolevLift hO hD 1 F0 x)

attribute [local irreducible] nativeFirstCorrectionLift

lemma contDiff_nativeFirstCorrectionLift (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) :
    ContDiff ℝ ∞ (nativeFirstCorrectionLift hF hO hD g L q R F0 j) := by
  unfold nativeFirstCorrectionLift
  have hz : ContDiff ℝ ∞ (fun x : R3 => (((q,x) : ℝ × R3),fderiv ℝ R x)) :=
    (contDiff_const.prodMk contDiff_id).prodMk (contDiff_infty_iff_fderiv.mp hR).2
  exact ((contDiff_referenceNativeMovingAdjointParametricCorrection hF hO hD g hg L 1 j).comp
    hz).clm_apply (contDiff_finiteCoreSobolevLift hO hD 1 F0)

/-- `F_j = I_{1→1/2} ∘ V_j` pointwise. -/
lemma nativeFirstCorrectionLift_inclusion_eq (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField) (L q : ℝ)
    (R : R3 → ℝ) (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) (x : R3) :
    sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num)
      (nativeFirstCorrectionLift hF hO hD g L q R F0 j x) =
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
        ((q,x),fderiv ℝ R x) j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 x)) := by
  let U : SphereSobolev (3/2 : ℝ) := finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 x
  let V : SphereSobolev 1 := finiteCoreSobolevLift hO hD 1 F0 x
  let Ihi1 : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev 1 :=
    sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num)
  let I1half : SphereSobolev 1 →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num)
  let C_hi : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
      ((q,x),fderiv ℝ R x) j
  let C_1 : SphereSobolev 1 →L[ℝ] SphereSobolev 1 :=
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L 1 ((q,x),fderiv ℝ R x) j
  have hu : Ihi1 U = V :=
    sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) 1 (by norm_num) F0 x
  have hc : Ihi1 (C_hi U) = C_1 (Ihi1 U) :=
    referenceNativeMovingAdjointParametricCorrection_inclusion hF hO hD g L (3/2 : ℝ) 1
      (by norm_num) ((q,x),fderiv ℝ R x) j U
  have hv : C_1 V = Ihi1 (C_hi U) := (congrArg C_1 hu).symm.trans hc.symm
  unfold nativeFirstCorrectionLift
  exact (congrArg I1half hv).trans
    (sphereSobolevInclusionL_comp_inclusionL_apply (3/2 : ℝ) 1 (1/2 : ℝ)
      (by norm_num) (by norm_num) (C_hi U))

/-- One native first-correction word `NU_ij(y) ∈ H^0` (MATHEMATICS.md, Section 2). -/
def nativeUFirstWord (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g) (L q δ A : ℝ)
    (p : ℕ) (hδ : 0 < δ) (hA : 0 < A) (F0 : smoothCompactFiniteSphereCore hO hD)
    (i j : Fin 3) (y : R3) : SphereSobolev 0 :=
  nativeOneWeightedHorizontalAction g L q (referenceRadius δ A p L)
      (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 j) y i +
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y) i
      (sphereSobolevZeroEquiv hO hD ((coreReferenceInput hO hD g hg L q δ A p j hδ hA F0).val y)) -
    (∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j •
      sphereSobolevInclusionL 1 0 (by norm_num)
        (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 k y)) +
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y) i
      (sphereSobolevInclusionL 1 0 (by norm_num)
        (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 j y))

/-- The actual native `SphereL2` output of the literal `UFirst` word. -/
def nativeUFirstOut (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g) (g2 : MatrixField)
    (L q δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A) (F0 : smoothCompactFiniteSphereCore hO hD)
    (y : R3) : SphereL2 :=
  (sphereSobolevZeroEquiv hO hD).symm
    (referenceRadius δ A p L y • (∑ i : Fin 3, ∑ j : Fin 3,
        referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
          nativeUFirstWord hF hO hD g hg L q δ A p hδ hA F0 i j y) +
      referenceRadius δ A p L y • (∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) •
        sphereSobolevInclusionL 1 0 (by norm_num)
          (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 i y)))

attribute [local irreducible] nativeUFirstWord nativeUFirstOut

/-! ### Termwise graph identities -/

lemma nativeOneWeightedHorizontalAction_firstCorrection_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) (y : R3) (i : Fin 3) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (nativeOneWeightedHorizontalAction g L q R
        (nativeFirstCorrectionLift hF hO hD g L q R F0 j) y i) =
    referenceLowerWeightedHorizontalAction g L q R
      (fun x => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 x))) y i := by
  have hFun : (fun x => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 x))) =
      (fun x => sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num)
        (nativeFirstCorrectionLift hF hO hD g L q R F0 j x)) :=
    funext (fun x => (nativeFirstCorrectionLift_inclusion_eq hF hO hD g L q R F0 j x).symm)
  rw [hFun]
  exact sphereSobolevInclusionL_nativeOneWeightedHorizontalAction g L q R _ y i
    ((contDiff_nativeFirstCorrectionLift hF hO hD g hg L q R hR F0 j).differentiable (by simp) y)

lemma correction_zero_coreReferenceInput_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L q δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A)
    (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) (i j : Fin 3) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
        ((q,y),fderiv ℝ (referenceRadius δ A p L) y) i
        (sphereSobolevZeroEquiv hO hD ((coreReferenceInput hO hD g hg L q δ A p j hδ hA F0).val y))) =
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
        ((q,y),fderiv ℝ (referenceRadius δ A p L) y) i
        (referenceHighWeightedHorizontalAction g L q (referenceRadius δ A p L)
          (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0) y j)) := by
  have hDict : referenceHighWeightedHorizontalAction g L q (referenceRadius δ A p L)
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0) y j =
      finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreReferenceInput hO hD g hg L q δ A p j hδ hA F0) y :=
    by simpa only [referenceHighWeightedHorizontalAction] using
      referenceHighWeightedHorizontalAction_finiteCoreSobolevLift hO hD g hg L q δ A p hδ hA F0 y j
  have hRep : sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
      (finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreReferenceInput hO hD g hg L q δ A p j hδ hA F0) y) =
      sphereSobolevZeroEquiv hO hD ((coreReferenceInput hO hD g hg L q δ A p j hδ hA F0).val y) :=
    (finiteCoreSobolevLift_representation hO hD (1/2 : ℝ) (by norm_num)
      (coreReferenceInput hO hD g hg L q δ A p j hδ hA F0)).2.2.2.1 y
  let V : SphereSobolev (1/2 : ℝ) :=
    referenceHighWeightedHorizontalAction g L q (referenceRadius δ A p L)
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0) y j
  let Ihalf0 : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let I0neg : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let C_half : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y) i
  let C_0 : SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0
      ((q,y),fderiv ℝ (referenceRadius δ A p L) y) i
  have hInput : Ihalf0 V =
      sphereSobolevZeroEquiv hO hD ((coreReferenceInput hO hD g hg L q δ A p j hδ hA F0).val y) :=
    (congrArg Ihalf0 hDict).trans hRep
  have hc : Ihalf0 (C_half V) = C_0 (Ihalf0 V) :=
    referenceNativeMovingAdjointParametricCorrection_inclusion hF hO hD g L (1/2 : ℝ) 0
      (by norm_num) ((q,y),fderiv ℝ (referenceRadius δ A p L) y) i V
  have hValue := (congrArg C_0 hInput).symm.trans hc.symm
  exact (congrArg I0neg hValue).trans
    (sphereSobolevInclusionL_comp_inclusionL_apply (1/2 : ℝ) 0 (-(1/2 : ℝ))
      (by norm_num) (by norm_num) (C_half V))

lemma nativeFirstCorrectionLift_drift_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField) (L q : ℝ)
    (R : R3 → ℝ) (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) (k : Fin 3) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevInclusionL 1 0 (by norm_num) (nativeFirstCorrectionLift hF hO hD g L q R F0 k y)) =
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,y),fderiv ℝ R y) k (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 y))) := by
  rw [← nativeFirstCorrectionLift_inclusion_eq, sphereSobolevInclusionL_comp_inclusionL_apply,
    sphereSobolevInclusionL_comp_inclusionL_apply]

lemma correction_zero_firstCorrection_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField) (L q : ℝ)
    (R : R3 → ℝ) (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) (i j : Fin 3) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0 ((q,y),fderiv ℝ R y) i
        (sphereSobolevInclusionL 1 0 (by norm_num)
          (nativeFirstCorrectionLift hF hO hD g L q R F0 j y))) =
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
          (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
            ((q,y),fderiv ℝ R y) j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 y)))) := by
  let V : SphereSobolev 1 := nativeFirstCorrectionLift hF hO hD g L q R F0 j y
  let I10 : SphereSobolev 1 →L[ℝ] SphereSobolev 0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let I1half : SphereSobolev 1 →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num)
  let I0neg : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let Ihalfneg : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let I1neg : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL 1 (-(1/2 : ℝ)) (by norm_num)
  let C_1 : SphereSobolev 1 →L[ℝ] SphereSobolev 1 :=
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L 1 ((q,y),fderiv ℝ R y) i
  let C_half : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
  let C_0 : SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0 ((q,y),fderiv ℝ R y) i
  have hc10 : I10 (C_1 V) = C_0 (I10 V) :=
    referenceNativeMovingAdjointParametricCorrection_inclusion hF hO hD g L 1 0
      (by norm_num) ((q,y),fderiv ℝ R y) i V
  have hcHalf : I1half (C_1 V) = C_half (I1half V) :=
    referenceNativeMovingAdjointParametricCorrection_inclusion hF hO hD g L 1 (1/2 : ℝ)
      (by norm_num) ((q,y),fderiv ℝ R y) i V
  have hLeft : I0neg (C_0 (I10 V)) = I1neg (C_1 V) :=
    (congrArg I0neg hc10.symm).trans
      (sphereSobolevInclusionL_comp_inclusionL_apply 1 0 (-(1/2 : ℝ))
        (by norm_num) (by norm_num) (C_1 V))
  have hRight : Ihalfneg (C_half (I1half V)) = I1neg (C_1 V) :=
    (congrArg Ihalfneg hcHalf.symm).trans
      (sphereSobolevInclusionL_comp_inclusionL_apply 1 (1/2 : ℝ) (-(1/2 : ℝ))
        (by norm_num) (by norm_num) (C_1 V))
  exact (hLeft.trans hRight.symm).trans
    (congrArg (fun v : SphereSobolev (1/2 : ℝ) => Ihalfneg (C_half v))
      (nativeFirstCorrectionLift_inclusion_eq hF hO hD g L q R F0 j y))

/-! ### Exact negative graph -/

/-- `K0 (UFirstOut y)` is exactly the literal `UFirst` of the full error dictionary
(same maps, coefficient order `Gamma i j k`, PLUS `f • shiftedDegree`). -/
theorem nativeUFirstOut_negative_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (g2 : MatrixField) (L q δ A : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hA : 0 < A) (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) :
    let R : R3 → ℝ := referenceRadius δ A p L
    let u : R3 → SphereSobolev (3/2 : ℝ) := finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
    let K : SphereL2 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
      (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
        (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
    let Iin : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let Iout : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let D := fun (i : Fin 3) (x : R3) => referenceHighWeightedHorizontalAction g L q R u x i
    let Fh := fun (i : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) i
    let Fl := fun i : Fin 3 => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
    let F := fun (i : Fin 3) (x : R3) => Iin (Fh i x (u x))
    let MF := fun i : Fin 3 => Iout.comp (Fl i)
    let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
    let b := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
    let Gamma := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j
    let r := R y
    let UF := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (F j) y i+
      MF i (D j y)-(∑ k : Fin 3, Gamma i j k • Iout (F k y))+MF i (F j y)
    let UFirst := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UF i j)+
      r • (∑ i : Fin 3, b i • Iout (F i y))
    K (nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0 y) = UFirst := by
  intro R u K Iin Iout D Fh Fl F MF Q b Gamma r UF UFirst
  have hR : ContDiff ℝ ∞ (referenceRadius δ A p L) :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ A p L hδ hA
  have hWord (i j : Fin 3) :
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (nativeUFirstWord hF hO hD g hg L q δ A p hδ hA F0 i j y) = UF i j := by
    simp only [nativeUFirstWord, map_add, map_sub, map_sum, map_smul,
      nativeOneWeightedHorizontalAction_firstCorrection_graph hF hO hD g hg L q
        (referenceRadius δ A p L) hR F0 j y i,
      correction_zero_coreReferenceInput_graph hF hO hD g hg L q δ A p hδ hA F0 y i j,
      nativeFirstCorrectionLift_drift_graph hF hO hD g L q (referenceRadius δ A p L) F0 y,
      correction_zero_firstCorrection_graph hF hO hD g L q (referenceRadius δ A p L) F0 y i j]
    try rfl
  have hK (v : SphereSobolev 0) : K ((sphereSobolevZeroEquiv hO hD).symm v) =
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) v := by
    show sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD ((sphereSobolevZeroEquiv hO hD).symm v)) = _
    rw [sphereSobolevZeroEquiv_apply_symm_apply]
  unfold nativeUFirstOut
  rw [hK]
  simp only [map_add, map_smul, map_sum, hWord,
    nativeFirstCorrectionLift_drift_graph hF hO hD g L q (referenceRadius δ A p L) F0 y]
  try rfl

/-! ### Support: the output vanishes where the finite input vanishes -/

theorem nativeUFirstOut_eq_zero_of_notMem_tsupport (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (g2 : MatrixField) (L q δ A : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hA : 0 < A) (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3)
    (hy : y ∉ tsupport (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0)) :
    nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0 y = 0 := by
  have hu : finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 =ᶠ[𝓝 y] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hy
  have hu1 : finiteCoreSobolevLift hO hD 1 F0 =ᶠ[𝓝 y] 0 := hu.mono (fun x hx => by
    have hx' : finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 x = 0 := hx
    show finiteCoreSobolevLift hO hD 1 F0 x = 0
    exact (sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) 1
      (by norm_num) F0 x).symm.trans
        ((congrArg (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num)) hx').trans (map_zero _)))
  have hV (j : Fin 3) :
      nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 j =ᶠ[𝓝 y] 0 :=
    hu1.mono (fun x hx => by
      have hx' : finiteCoreSobolevLift hO hD 1 F0 x = 0 := hx
      show nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 j x = 0
      unfold nativeFirstCorrectionLift
      exact (congrArg (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 1
        ((q,x),fderiv ℝ (referenceRadius δ A p L) x) j) hx').trans (map_zero _))
  have hV0 (j : Fin 3) :
      nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 j y = 0 :=
    (hV j).self_of_nhds
  have hdV (j : Fin 3) :
      fderiv ℝ (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 j) y = 0 :=
    (hV j).fderiv_eq.trans (fderiv_const_apply 0)
  have hu0 : finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 y = 0 := hu.self_of_nhds
  have hdu : fderiv ℝ (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0) y = 0 :=
    hu.fderiv_eq.trans (fderiv_const_apply 0)
  have hD0 (j : Fin 3) : referenceHighWeightedHorizontalAction g L q (referenceRadius δ A p L)
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0) y j = 0 := by
    simp only [referenceHighWeightedHorizontalAction, referenceHighHorizontalAction, hdu, hu0,
      ContinuousLinearMap.zero_apply, map_zero, smul_zero, add_zero]
  have hZG (j : Fin 3) :
      sphereSobolevZeroEquiv hO hD ((coreReferenceInput hO hD g hg L q δ A p j hδ hA F0).val y) = 0 := by
    have hDict : referenceHighWeightedHorizontalAction g L q (referenceRadius δ A p L)
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0) y j =
        finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreReferenceInput hO hD g hg L q δ A p j hδ hA F0) y :=
      by simpa only [referenceHighWeightedHorizontalAction] using
      referenceHighWeightedHorizontalAction_finiteCoreSobolevLift hO hD g hg L q δ A p hδ hA F0 y j
    have hRep : sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreReferenceInput hO hD g hg L q δ A p j hδ hA F0) y) =
        sphereSobolevZeroEquiv hO hD ((coreReferenceInput hO hD g hg L q δ A p j hδ hA F0).val y) :=
      (finiteCoreSobolevLift_representation hO hD (1/2 : ℝ) (by norm_num)
        (coreReferenceInput hO hD g hg L q δ A p j hδ hA F0)).2.2.2.1 y
    exact hRep.symm.trans
      ((congrArg (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num))
        (hDict.symm.trans (hD0 j))).trans (map_zero _))
  unfold nativeUFirstOut
  simp only [nativeUFirstWord, nativeOneWeightedHorizontalAction, hdV, hV0, hZG,
    ContinuousLinearMap.zero_apply, map_zero, smul_zero, add_zero, sub_zero,
    Finset.sum_const_zero]

theorem tsupport_nativeUFirstOut_subset (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (g2 : MatrixField) (L q δ A : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hA : 0 < A) (F0 : smoothCompactFiniteSphereCore hO hD) :
    tsupport (nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0) ⊆
        tsupport (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0) ∧
      tsupport (nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0) ⊆ tsupport F0.val ∧
      HasCompactSupport (nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0) := by
  have hRep := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F0
  have hSub : tsupport (nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0) ⊆
      tsupport (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0) := by
    apply closure_minimal ?_ (isClosed_tsupport _)
    intro y hy
    by_contra hOut
    exact (Function.mem_support.mp hy)
      (nativeUFirstOut_eq_zero_of_notMem_tsupport hF hO hD g hg g2 L q δ A p hδ hA F0 y hOut)
  exact ⟨hSub, hSub.trans hRep.2.2.1,
    IsCompact.of_isClosed_subset hRep.2.1 (isClosed_tsupport _) hSub⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
