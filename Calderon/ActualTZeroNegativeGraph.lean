import Calderon.ActualTFirstPhysicalDictionary
import Calderon.ActualFiniteHarmonicModelReferenceAdjointZeroRaw
import Calderon.ActualHorizontalSobolevConnection

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroNegativeGraph
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph ActualFiniteHarmonicCore
  ActualFiniteHarmonicModel ActualAngularHighDraft ActualAngularPiDraft ActualHigherSPhysicalPairing
  ActualFiniteCoreLoweringRealization ActualTFirstPhysicalDictionary
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds AmbientReferenceRaising
  SmoothSphereRotationProjection ConformalDepth

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "DL" => sphereSobolevShiftedDegreeL (3/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

/-- The original finite-input Sobolev lift, evaluated at a point, as a linear map. -/
def finiteCoreSobolevEvaluation (s : ℝ) (x : R3) :
    smoothCompactFiniteSphereCore hO hD →ₗ[ℝ] SphereSobolev s where
  toFun F := finiteCoreSobolevLift hO hD s F x
  map_add' F G := by
    apply sphereSobolev_ext s
    intro k
    simp only [sphereSobolevCoefficientL_finiteCoreSobolevLift,map_add,Submodule.coe_add,Pi.add_apply]
  map_smul' c F := by
    apply sphereSobolev_ext s
    intro k
    simp only [sphereSobolevCoefficientL_finiteCoreSobolevLift,map_smul,Submodule.coe_smul,
      Pi.smul_apply,RingHom.id_apply]

local notation "EV" => finiteCoreSobolevEvaluation hO hD

private lemma evaluation_scalar (s : ℝ) (x : R3) (c : R3 → ℝ)
    (hc : ContDiff ℝ ∞ c) (F : smoothCompactFiniteSphereCore hO hD) :
    EV s x (coreScalar hO hD c hc F)=c x • EV s x F := by
  change finiteCoreSobolevLift hO hD s (coreScalar hO hD c hc F) x =
    c x • finiteCoreSobolevLift hO hD s F x
  apply sphereSobolev_ext s
  intro k
  simp only [sphereSobolevCoefficientL_finiteCoreSobolevLift,map_smul,coreScalar,
    LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk]

private lemma evaluation_rotation (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (a b : Fin 3) :
    EV (1/2 : ℝ) x (coreRotation hO hD a b F)=
      sphereSobolevRotationL (3/2 : ℝ) a b (EV (3/2 : ℝ) x F) := by
  change finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreRotation hO hD a b F) x = _
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  rw [sphereSobolevCoefficientL_finiteCoreSobolevLift,coreRotation,coreBlockOperator_coordinate]
  have hIndex := congrArg (fun t : ℝ => sphereSobolevCoefficientL t k
    (sphereSobolevRotationL (3/2 : ℝ) a b (EV (3/2 : ℝ) x F)))
    (show (3/2 : ℝ)-1=(1/2 : ℝ) by norm_num)
  have h := sphereSobolevCoefficientL_rotation (3/2 : ℝ) a b k (EV (3/2 : ℝ) x F)
  exact (hIndex.symm.trans (h.trans (congrArg (harmonicSphereRotation k a b)
    (sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (3/2 : ℝ) F x k)))).symm

private lemma evaluation_degree (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    EV (1/2 : ℝ) x (coreDegree hO hD F)=DL (EV (3/2 : ℝ) x F) := by
  change finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreDegree hO hD F) x = _
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  rw [sphereSobolevCoefficientL_finiteCoreSobolevLift,coreDegree,coreWeightOperator_graph]
  have hIndex := congrArg (fun t : ℝ => sphereSobolevCoefficientL t k
    (DL (EV (3/2 : ℝ) x F)))
    (show (3/2 : ℝ)-1=(1/2 : ℝ) by norm_num)
  have h := sphereSobolevCoefficientL_shiftedDegree (3/2 : ℝ) k (EV (3/2 : ℝ) x F)
  exact (hIndex.symm.trans (h.trans (congrArg (fun v : harmonicSphereSubspace k => (k : ℝ) • v)
    (sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (3/2 : ℝ) F x k)))).symm

private lemma evaluation_inclusion (s t : ℝ) (hts : t ≤ s)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    sphereSobolevInclusionL s t hts (EV s x F)=EV t x F :=
  sphereSobolevInclusionL_finiteCoreSobolevLift hO hD s t hts F x

private lemma evaluation_raising_negative (hF : SphereFischerInner)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (i : Fin 3) :
    EV (-(1/2 : ℝ)) x (coreRaising hO hD hF i F)=
      raisingLow hF hO hD i (EV (1/2 : ℝ) x F) := by
  have hRaise := sphereSobolevAngularCoordinateTranspose_threeHalf_finiteCore hF hO hD F x i
  change raisingHigh hF hO hD i (EV (3/2 : ℝ) x F)=
    EV (1/2 : ℝ) x (coreRaising hO hD hF i F) at hRaise
  calc
    _ = JL (EV (1/2 : ℝ) x (coreRaising hO hD hF i F)) :=
      (evaluation_inclusion hO hD _ _ (by norm_num) _ x).symm
    _ = JL (raisingHigh hF hO hD i (EV (3/2 : ℝ) x F)) := congrArg JL hRaise.symm
    _ = raisingLow hF hO hD i (IH (EV (3/2 : ℝ) x F)) :=
      v017_inclusion_raisingHigh hF hO hD i _
    _ = _ := congrArg (raisingLow hF hO hD i) (evaluation_inclusion hO hD _ _ (by norm_num) F x)

private lemma evaluation_derivative_negative (hF : SphereFischerInner)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (i : Fin 3) :
    EV (-(1/2 : ℝ)) x (coreDerivative hO hD hF i F)=
      loweringLow hF hO hD i (EV (1/2 : ℝ) x F) := by
  let KL := sphereSobolevHalfToSphereL2L hO hD
  let ZE := sphereSobolevZeroEquiv hO hD
  have hDecode := halfToSphereL2_finiteCoreLift hO hD (coreDerivative hO hD hF i F) x
  rw [sphereSobolevInclusionL_finiteCoreSobolevLift] at hDecode
  have hLower := loweringHigh_finiteCore_decode hO hD hF F x i
  have hCoarse := congrArg ZE (hLower.trans hDecode.symm)
  simp only [ZE,zeroEquiv_halfToSphereL2] at hCoarse
  have hHalf : loweringHigh hF hO hD i (EV (3/2 : ℝ) x F)=
      EV (1/2 : ℝ) x (coreDerivative hO hD hF i F) :=
    sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num) hCoarse
  calc
    _ = JL (EV (1/2 : ℝ) x (coreDerivative hO hD hF i F)) :=
      (evaluation_inclusion hO hD _ _ (by norm_num) _ x).symm
    _ = JL (loweringHigh hF hO hD i (EV (3/2 : ℝ) x F)) := congrArg JL hHalf.symm
    _ = loweringLow hF hO hD i (IH (EV (3/2 : ℝ) x F)) :=
      v017_inclusion_loweringHigh hF hO hD i _
    _ = _ := congrArg (loweringLow hF hO hD i) (evaluation_inclusion hO hD _ _ (by norm_num) F x)

private lemma evaluation_connection (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) (i : Fin 3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    EV (1/2 : ℝ) x (nativeReferenceConnectionAction hO hD g hg L q i F)=
      referenceHighHorizontalAngularL g L q x i (EV (3/2 : ℝ) x F) := by
  simp only [nativeReferenceConnectionAction,LinearMap.smul_apply,LinearMap.sum_apply,
    Module.End.mul_apply,map_smul,map_sum,evaluation_scalar,evaluation_rotation,
    referenceHighHorizontalAngularL,_root_.smul_apply,_root_.sum_apply]

variable (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
  (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)

local notation "fi" => (fun (i : Fin 3) (x : R3) => referenceFrameDerivative g L q i
  (fun y => Real.log (referenceRadius dr Ar p L y)) x)
local notation "Gamma" => (fun (i : Fin 3) (x : R3) => referenceHighHorizontalAngularL g L q x i)

/-- Full original T zero part as a genuine Hi-to-negative map. -/
def referenceZeroNegative (x : R3) : Hi →L[ℝ] Neg :=
  ∑ i : Fin 3, (raisingLow hF hO hD i).comp (Gamma i x+fi i x • DL)

/-- Full RAW Tdag zero part; the original degree offset N-1 is retained. -/
def referenceAdjointZeroNegative (x : R3) : Hi →L[ℝ] Neg :=
  ∑ i : Fin 3, (loweringLow hF hO hD i).comp (-Gamma i x+fi i x • (DL-IH))

attribute [local irreducible] raisingLow loweringLow raisingHigh loweringHigh
  sphereSobolevInclusionL sphereSobolevRotationL sphereSobolevShiftedDegreeL
  nativeReferenceConnectionAction referenceHighHorizontalAngularL coreRaising coreDerivative

theorem native_zero_negative_graph (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    JL (finiteCoreSobolevLift hO hD (1/2 : ℝ)
      (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F) x) =
      referenceZeroNegative hO hD hF g L q dr Ar p x
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) := by
  change JL (EV (1/2 : ℝ) x (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F))=_
  rw [evaluation_inclusion hO hD]
  simp only [nativeReferenceZeroCoefficient,LinearMap.sum_apply,LinearMap.add_apply,
    nativeReferenceProfileScalar,Module.End.mul_apply,
    map_sum,evaluation_raising_negative,map_add,map_smul,evaluation_connection,
    evaluation_scalar,evaluation_degree,referenceZeroNegative,_root_.sum_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,_root_.smul_apply]
  simp only [finiteCoreSobolevEvaluation,LinearMap.coe_mk,AddHom.coe_mk]

theorem native_adjoint_zero_negative_graph (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    JL (finiteCoreSobolevLift hO hD (1/2 : ℝ)
      (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F) x) =
      referenceAdjointZeroNegative hO hD hF g L q dr Ar p x
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) := by
  change JL (EV (1/2 : ℝ) x (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F))=_
  rw [evaluation_inclusion hO hD,
    nativeReferenceAdjointZeroCoefficient_eq_raw hO hD hF g hg L q dr Ar p hdr hAr]
  simp only [LinearMap.sum_apply,LinearMap.add_apply,LinearMap.neg_apply,
    nativeReferenceProfileScalar,Module.End.mul_apply,map_sum,evaluation_derivative_negative,
    map_add,map_neg,map_sub,LinearMap.sub_apply,Module.End.one_apply,evaluation_scalar,
    evaluation_connection,evaluation_degree,referenceAdjointZeroNegative,_root_.sum_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sub_apply,_root_.smul_apply,evaluation_inclusion]
  simp only [finiteCoreSobolevEvaluation,LinearMap.coe_mk,AddHom.coe_mk,
    sphereSobolevInclusionL_finiteCoreSobolevLift,smul_sub,map_smul,map_sub]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroNegativeGraph

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroNegativeGraph.native_zero_negative_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroNegativeGraph.native_adjoint_zero_negative_graph
