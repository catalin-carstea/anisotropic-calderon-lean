import Calderon.ActualPhysicalLowResidualUFirst
import Calderon.ActualHorizontalGeometry
import Calderon.ActualDensityPrincipalFrameSmoothness
import Calderon.ActualNormalizedSecondMetricDrift

/-! The actual native `UFirst` output is `C^∞`, and its weighted norm
square is integrable against every continuous weight. Joint geometry is taken from
`contDiff_referenceMetricGramFrame` and `contDiff_referenceFrameConnectionJoint`. -/
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
  PrincipalCommutator BoundedAngularShift ActualHorizontalNormBridge

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevZeroEquiv
  sphereSobolevRotationL sphereSobolevShiftedDegreeL finiteCoreSobolevLift
  coreReferenceInput referenceNativeMovingAdjointParametricCorrection
  referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint
  referenceFrameConnectionCoefficient referenceMetricGramFrame referenceRadiusHorizontalLogDerivative
  nativeOneHorizontalAngularL nativeOneShiftedDegreeL nativeOneWeightedHorizontalAction
  nativeFirstCorrectionLift nativeUFirstWord nativeUFirstOut

/-! ### Actual geometric coefficients on a `q`-slice -/

/-- The exact sliced Gram connection coefficient along the actual frame is `C^∞` in `x`. -/
lemma contDiff_referenceFrameConnectionCoefficient_gramFrame (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L q : ℝ) (i a b : Fin 3) :
    ContDiff ℝ ∞ (fun x : R3 => referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) a b) := by
  have hX : ContDiff ℝ ∞ (fun z : ℝ × R3 => referenceMetricGramFrame g L z i) :=
    contDiff_referenceMetricGramFrame g hg L i
  have hJ := (contDiff_referenceFrameConnectionJoint g hg L
    (fun z : ℝ × R3 => referenceMetricGramFrame g L z i) hX a b).comp
      (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun x : R3 => ((q,x) : ℝ × R3)))
  convert hJ using 1
  funext x
  exact (referenceFrameConnectionJoint_eq g hg L
    (fun z : ℝ × R3 => referenceMetricGramFrame g L z i) (q,x) a b).symm

/-- The actual horizontal log-derivative `f_i` of the actual radius is `C^∞` in `x`. -/
lemma contDiff_referenceRadiusHorizontalLogDerivative_actual (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L q δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => referenceRadiusHorizontalLogDerivative g L q
      (referenceRadius δ A p L) x i) := by
  have hR : ContDiff ℝ ∞ (referenceRadius δ A p L) :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ A p L hδ hA
  refine contDiff_iff_contDiffAt.mpr (fun y => ?_)
  exact (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg (referenceRadius δ A p L) (q,y) i
    hR.contDiffAt (referenceRadius_pos δ A p L y hδ hA).ne').comp y
      (contDiffAt_const.prodMk contDiffAt_id)

/-- The native weighted action of a `C^∞` field is `C^∞` (derivative, connection, PLUS `f_i • Deg`). -/
lemma contDiff_nativeOneWeightedHorizontalAction (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A) (V : R3 → SphereSobolev 1)
    (hV : ContDiff ℝ ∞ V) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y => nativeOneWeightedHorizontalAction g L q (referenceRadius δ A p L) V y i) := by
  have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ V y (referenceMetricGramFrame g L (q,y) i)) :=
    (hV.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_referenceMetricGramFrame_slice g hg L q i)
  have hI : ContDiff ℝ ∞ (fun y => sphereSobolevInclusionL 1 0 (by norm_num)
      (fderiv ℝ V y (referenceMetricGramFrame g L (q,y) i))) :=
    contDiff_const.clm_apply hd
  have hAng : ContDiff ℝ ∞ (fun y => nativeOneHorizontalAngularL g L q y i (V y)) := by
    have hRot (a b : Fin 3) : ContDiff ℝ ∞ (fun y : R3 => sphereSobolevRotationL 1 a b (V y)) :=
      contDiff_const.clm_apply hV
    have hSum : ContDiff ℝ ∞ (fun y : R3 => (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
        referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) a b •
          sphereSobolevRotationL 1 a b (V y)) :=
      (ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
        (contDiff_referenceFrameConnectionCoefficient_gramFrame g hg L q i a b).smul (hRot a b)))).const_smul (1/2 : ℝ)
    have hApplied : ContDiff ℝ ∞ (fun y : R3 =>
        sphereSobolevInclusionL ((1:ℝ)-1) 0 (by norm_num)
          ((1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
            referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) a b •
              sphereSobolevRotationL 1 a b (V y))) := contDiff_const.clm_apply hSum
    simpa only [nativeOneHorizontalAngularL, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply] using hApplied
  have hDeg : ContDiff ℝ ∞ (fun y => referenceRadiusHorizontalLogDerivative g L q
      (referenceRadius δ A p L) y i • nativeOneShiftedDegreeL (V y)) :=
    (contDiff_referenceRadiusHorizontalLogDerivative_actual g hg L q δ A p hδ hA i).smul
      (contDiff_const.clm_apply hV)
  unfold nativeOneWeightedHorizontalAction
  exact (hI.add hAng).add hDeg

/-! ### The literal word and output -/

lemma contDiff_correction_along_radius (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g) (L q s : ℝ)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x : R3 =>
      referenceNativeMovingAdjointParametricCorrection hF hO hD g L s ((q,x),fderiv ℝ R x) i) := by
  have hz : ContDiff ℝ ∞ (fun x : R3 => (((q,x) : ℝ × R3),fderiv ℝ R x)) :=
    (contDiff_const.prodMk contDiff_id).prodMk (contDiff_infty_iff_fderiv.mp hR).2
  exact (contDiff_referenceNativeMovingAdjointParametricCorrection hF hO hD g hg L s i).comp hz

lemma contDiff_zeroEquiv_coreReferenceInput (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g) (L q δ A : ℝ)
    (p : ℕ) (hδ : 0 < δ) (hA : 0 < A) (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) :
    ContDiff ℝ ∞ (fun y =>
      sphereSobolevZeroEquiv hO hD ((coreReferenceInput hO hD g hg L q δ A p j hδ hA F0).val y)) :=
  (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp
    (coreReferenceInput hO hD g hg L q δ A p j hδ hA F0).property.1

theorem contDiff_nativeUFirstWord (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g) (L q δ A : ℝ)
    (p : ℕ) (hδ : 0 < δ) (hA : 0 < A) (F0 : smoothCompactFiniteSphereCore hO hD) (i j : Fin 3) :
    ContDiff ℝ ∞ (nativeUFirstWord hF hO hD g hg L q δ A p hδ hA F0 i j) := by
  have hR : ContDiff ℝ ∞ (referenceRadius δ A p L) :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ A p L hδ hA
  have hV (k : Fin 3) := contDiff_nativeFirstCorrectionLift hF hO hD g hg L q
    (referenceRadius δ A p L) hR F0 k
  have hIV (k : Fin 3) : ContDiff ℝ ∞ (fun y => sphereSobolevInclusionL 1 0 (by norm_num)
      (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 k y)) :=
    contDiff_const.clm_apply (hV k)
  have hC0 := contDiff_correction_along_radius hF hO hD g hg L q 0 (referenceRadius δ A p L) hR i
  have h1 := contDiff_nativeOneWeightedHorizontalAction g hg L q δ A p hδ hA _ (hV j) i
  have h2 := hC0.clm_apply (contDiff_zeroEquiv_coreReferenceInput hO hD g hg L q δ A p hδ hA F0 j)
  have h3 : ContDiff ℝ ∞ (fun y => ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j •
        sphereSobolevInclusionL 1 0 (by norm_num)
          (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 k y)) :=
    ContDiff.sum (fun k _ =>
      (contDiff_referenceFrameConnectionCoefficient_gramFrame g hg L q i k j).smul (hIV k))
  have h4 := hC0.clm_apply (hIV j)
  unfold nativeUFirstWord
  exact ((h1.add h2).sub h3).add h4

/-- The actual native output of the literal `UFirst` word is `C^∞`. -/
theorem contDiff_nativeUFirstOut (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (L q δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A)
    (F0 : smoothCompactFiniteSphereCore hO hD) :
    ContDiff ℝ ∞ (nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0) := by
  have hR : ContDiff ℝ ∞ (referenceRadius δ A p L) :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ A p L hδ hA
  have hslice : ContDiff ℝ ∞ (fun x : R3 => ((q,x) : ℝ × R3)) :=
    contDiff_const.prodMk contDiff_id
  have hQ (i j : Fin 3) : ContDiff ℝ ∞ (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) :=
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp hslice
  have hb (i : Fin 3) : ContDiff ℝ ∞ (fun y => normalizedSecondDriftFrameJoint g g2 L i (q,y)) :=
    (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).comp hslice
  have hIV (k : Fin 3) : ContDiff ℝ ∞ (fun y => sphereSobolevInclusionL 1 0 (by norm_num)
      (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 k y)) :=
    contDiff_const.clm_apply
      (contDiff_nativeFirstCorrectionLift hF hO hD g hg L q (referenceRadius δ A p L) hR F0 k)
  have hW : ContDiff ℝ ∞ (fun y => referenceRadius δ A p L y • (∑ i : Fin 3, ∑ j : Fin 3,
        referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
          nativeUFirstWord hF hO hD g hg L q δ A p hδ hA F0 i j y) +
      referenceRadius δ A p L y • (∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) •
        sphereSobolevInclusionL 1 0 (by norm_num)
          (nativeFirstCorrectionLift hF hO hD g L q (referenceRadius δ A p L) F0 i y))) :=
    (hR.smul (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
      (hQ i j).smul (contDiff_nativeUFirstWord hF hO hD g hg L q δ A p hδ hA F0 i j))))).add
    (hR.smul (ContDiff.sum (fun i _ => (hb i).smul (hIV i))))
  unfold nativeUFirstOut
  exact (sphereSobolevZeroEquiv hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp hW

theorem continuous_nativeUFirstOut (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (L q δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A)
    (F0 : smoothCompactFiniteSphereCore hO hD) :
    Continuous (nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0) :=
  (contDiff_nativeUFirstOut hF hO hD g hg g2 hg2 L q δ A p hδ hA F0).continuous

/-! ### Weighted integrability -/

theorem integrable_weighted_norm_sq_nativeUFirstOut (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (L q δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A) (F0 : smoothCompactFiniteSphereCore hO hD)
    (ρ : R3 → ℝ) (hρ : Continuous ρ) :
    Integrable (fun x => ρ x * ‖nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0 x‖^2) := by
  set U := nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0 with hUdef
  have hU : Continuous U := continuous_nativeUFirstOut hF hO hD g hg g2 hg2 L q δ A p hδ hA F0
  have hcs : HasCompactSupport U := (tsupport_nativeUFirstOut_subset hF hO hD g hg g2 L q δ A p hδ hA F0).2.2
  have hsub : Function.support (fun x => ρ x * ‖U x‖^2) ⊆ tsupport U := by
    intro x hx
    apply subset_tsupport
    intro h0
    apply hx
    simp [h0]
  have hcs' : HasCompactSupport (fun x => ρ x * ‖U x‖^2) :=
    IsCompact.of_isClosed_subset hcs (isClosed_tsupport _)
      (closure_minimal hsub (isClosed_tsupport _))
  exact (hρ.mul (hU.norm.pow 2)).integrable_of_hasCompactSupport hcs'

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
