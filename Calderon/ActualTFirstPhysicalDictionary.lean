import Calderon.ActualFiniteCoreLoweringRealization
import Calderon.ActualTSShiftedAdjointDictionary
import Calderon.ActualFinitePhysicalModelErrorDictionary

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTFirstPhysicalDictionary
open SphereHarmonic SpectralCoreRegularity ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualHigherSPhysicalPairing ActualFiniteCoreLoweringRealization
  PrincipalCommutator ActualModelCommutatorWords SmoothMetricFrame MovingFrameConnection
  ActualAngularPiDraft ReferenceDensityBounds

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD

/-- Original finite-input Sobolev lifting commutes with every base derivative. -/
theorem finiteCoreLift_directionalDerivative (s : ℝ) (v : R3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    finiteCoreSobolevLift hO hD s (coreDirectionalDerivative hO hD v F) x =
      fderiv ℝ (finiteCoreSobolevLift hO hD s F) x v := by
  let U := finiteCoreSobolevLift hO hD s F
  have hU := (contDiff_finiteCoreSobolevLift hO hD s F).differentiable (by simp) x
  have hF := F.property.1.differentiable (by simp) x
  apply sphereSobolev_ext s
  intro k
  have hFunction : (fun y : R3 => sphereSobolevCoefficientL s k (U y)) =
      (fun y : R3 => sphereHarmonicCoordinate hO hD k (F.val y)) :=
    funext (fun y => sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD s F y k)
  have hNative := congrArg (fun A : R3 →L[ℝ] harmonicSphereSubspace k => A v)
    (((sphereSobolevCoefficientL s k).hasFDerivAt.comp x hU.hasFDerivAt).fderiv)
  have hFun := congrArg
    (fun z : R3 → harmonicSphereSubspace k => fderiv ℝ z x v) hFunction
  have hCore := congrArg (fun A : R3 →L[ℝ] harmonicSphereSubspace k => A v)
    (fderiv_sphereHarmonicCoordinate hO hD k F.val x hF)
  rw [sphereSobolevCoefficientL_finiteCoreSobolevLift]
  change sphereHarmonicCoordinate hO hD k (fderiv ℝ F.val x v) = _
  simpa only [ContinuousLinearMap.comp_apply,Function.comp_def,U]
    using (hNative.symm.trans (hFun.trans hCore)).symm

/-- Full raising output decoded to the original finite-core field. -/
theorem raisingHigh_finiteCore_decode (hF : SphereFischerInner)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (i : Fin 3) :
    KL (raisingHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)) =
      (coreRaising hO hD hF i F).val x := by
  have h := sphereSobolevAngularCoordinateTranspose_threeHalf_finiteCore hF hO hD F x i
  change raisingHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) =
    finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreRaising hO hD hF i F) x at h
  rw [h]
  have hDecode := halfToSphereL2_finiteCoreLift hO hD (coreRaising hO hD hF i F) x
  rw [sphereSobolevInclusionL_finiteCoreSobolevLift] at hDecode
  exact hDecode

variable (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
  (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)

/-- Literal first-base part of the original T, in the original Half space. -/
def referenceFirstHalf (U : R3 → Hi) (x : R3) : Half :=
  ∑ l : Fin 3, ∑ i : Fin 3,
    referenceMetricGramFrame g L (q,x) i l •
      raisingHigh hF hO hD i (fderiv ℝ U x (coordinateDirection l))

/-- Literal first-base part of original Tdag, including its negative sign. -/
def referenceAdjointFirstHalf (U : R3 → Hi) (x : R3) : Half :=
  -(∑ l : Fin 3, ∑ i : Fin 3,
    referenceMetricGramFrame g L (q,x) i l •
      loweringHigh hF hO hD i (fderiv ℝ U x (coordinateDirection l)))

theorem native_first_coordinate_decode
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (l : Fin 3) :
    (nativeReferenceFirstCoefficient hO hD hF g hg L q dr Ar p hdr hAr l F).val x =
      KL (∑ i : Fin 3, referenceMetricGramFrame g L (q,x) i l •
        raisingHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)) := by
  have hCentral (i : Fin 3) :
      Commute (coreRaising hO hD hF i) (nativeReferenceFrameScalar hO hD g hg L q i l) :=
    scalarCentral_coreRaising hO hD hF i _ _
  have hRow (i : Fin 3) :
      (coreRaising hO hD hF i (nativeReferenceFrameScalar hO hD g hg L q i l F)).val x =
        referenceMetricGramFrame g L (q,x) i l • (coreRaising hO hD hF i F).val x := by
    have h := congrArg (fun A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) =>
      (A F).val x) (hCentral i).eq
    exact h
  simp only [nativeReferenceFirstCoefficient,LinearMap.sum_apply,Submodule.coe_sum,
    Finset.sum_apply,Module.End.mul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact (hRow i).trans (congrArg (fun z : SphereL2 =>
    referenceMetricGramFrame g L (q,x) i l • z)
    (raisingHigh_finiteCore_decode hO hD hF F x i).symm)

theorem native_adjoint_first_coordinate_decode
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (l : Fin 3) :
    (nativeReferenceAdjointFirstCoefficient hO hD hF g hg L q dr Ar p hdr hAr l F).val x =
      KL (-(∑ i : Fin 3, referenceMetricGramFrame g L (q,x) i l •
        loweringHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x))) := by
  have hCentral (i : Fin 3) :
      Commute (coreDerivative hO hD hF i) (nativeReferenceFrameScalar hO hD g hg L q i l) :=
    scalarCentral_coreDerivative hO hD hF i _ _
  have hRow (i : Fin 3) :
      (coreDerivative hO hD hF i (nativeReferenceFrameScalar hO hD g hg L q i l F)).val x =
        referenceMetricGramFrame g L (q,x) i l • (coreDerivative hO hD hF i F).val x :=
    congrArg (fun A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) =>
      (A F).val x) (hCentral i).eq
  rw [ActualTSShiftedAdjointDictionary.native_adjoint_first_coefficient_eq
    hO hD hF g hg L q dr Ar p hdr hAr l]
  simp only [LinearMap.neg_apply,LinearMap.sum_apply,Submodule.coe_neg,Submodule.coe_sum,
    Pi.neg_apply,Finset.sum_apply,Module.End.mul_apply,map_neg,map_sum,map_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (hRow i).trans (congrArg (fun z : SphereL2 =>
    referenceMetricGramFrame g L (q,x) i l • z)
    (loweringHigh_finiteCore_decode hO hD hF F x i).symm)

/-- Original T with its unchanged full zero coefficient. -/
theorem nativeT_eq_first_and_original_zero
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (nativeT hO hD hF g hg L q dr Ar p hdr hAr F).val x =
      KL (referenceFirstHalf hO hD hF g L q
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) x) +
      (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x := by
  rw [nativeT_eq_modelFirstOrder hO hD hF g hg L q dr Ar p hdr hAr]
  simp only [modelFirstOrder,LinearMap.add_apply,LinearMap.sum_apply,Module.End.mul_apply,
    Submodule.coe_add,Submodule.coe_sum,Pi.add_apply,Finset.sum_apply,
    referenceFirstHalf,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [native_first_coordinate_decode hO hD hF g hg L q dr Ar p hdr hAr,
    finiteCoreLift_directionalDerivative hO hD]
  simp only [map_neg,map_sum,Finset.sum_neg_distrib]

/-- Original raw Tdag zero coefficient remains; the separately charged Z is not added. -/
theorem nativeTdag_eq_first_and_original_zero
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (nativeTdag hO hD hF g hg L q dr Ar p hdr hAr F).val x =
      KL (referenceAdjointFirstHalf hO hD hF g L q
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) x) +
      (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x := by
  rw [nativeTdag_eq_modelFirstOrder hO hD hF g hg L q dr Ar p hdr hAr]
  simp only [modelFirstOrder,LinearMap.add_apply,LinearMap.sum_apply,Module.End.mul_apply,
    Submodule.coe_add,Submodule.coe_sum,Pi.add_apply,Finset.sum_apply,
    referenceAdjointFirstHalf,map_neg,map_sum,Finset.sum_neg_distrib]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [native_adjoint_first_coordinate_decode hO hD hF g hg L q dr Ar p hdr hAr,
    finiteCoreLift_directionalDerivative hO hD]
  simp only [map_neg,map_sum,Finset.sum_neg_distrib]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTFirstPhysicalDictionary

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTFirstPhysicalDictionary.finiteCoreLift_directionalDerivative
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTFirstPhysicalDictionary.nativeT_eq_first_and_original_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTFirstPhysicalDictionary.nativeTdag_eq_first_and_original_zero
