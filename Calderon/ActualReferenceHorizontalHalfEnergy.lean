import Calderon.ActualNativePhysicalModelInputDictionary
import Calderon.ActualLowerSSelfFormation
import Calderon.SphereSobolevHalfWeightedGraphLowering

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualFiniteHarmonicAmbient
  ConnectionError NormalCoordinatesFrame SmoothMetricFrame MovingFrameConnection
  AmbientReferenceRaising RadiusProfile ConformalDepth SmoothSphereRotationProjection

/-- The raw physical reference horizontal action lies at the exact Half derivative
scale measured by the original finite-core profile energy. -/
lemma referenceHighHorizontalAction_finiteCoreSobolevLift
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (y : R3) (i : Fin 3) :
    referenceHighHorizontalAction g L q (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) y i =
      finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreReferenceHorizontal hO hD g hg L q i F) y := by
  let U := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  let X := referenceMetricGramFrame g L (q,y) i
  let Gamma := fun a b : Fin 3 => referenceFrameConnectionCoefficient g L q y X a b
  have hUSmooth : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hUDiff := hUSmooth.differentiable (by simp) y
  have hFDiff := F.property.1.differentiable (by simp) y
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  let c := sphereHarmonicCoordinate hO hD k
  let v := c (F.val y)
  have hFunction : (fun x : R3 => sphereSobolevCoefficientL (3/2 : ℝ) k (U x)) =
      (fun x : R3 => c (F.val x)) :=
    funext (fun x => sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (3/2 : ℝ) F x k)
  have hNativeDerivative := congrArg
    (fun T : R3 →L[ℝ] harmonicSphereSubspace k => T X)
    (((sphereSobolevCoefficientL (3/2 : ℝ) k).hasFDerivAt.comp y hUDiff.hasFDerivAt).fderiv)
  have hFunctionDerivative := congrArg
    (fun V : R3 → harmonicSphereSubspace k => fderiv ℝ V y X) hFunction
  have hCoreDerivative := congrArg
    (fun T : R3 →L[ℝ] harmonicSphereSubspace k => T X)
    (fderiv_sphereHarmonicCoordinate hO hD k F.val y hFDiff)
  have hBase : sphereSobolevCoefficientL (3/2 : ℝ) k (fderiv ℝ U y X) =
      c (fderiv ℝ F.val y X) := by
    simpa (config := { instances := true }) only [ContinuousLinearMap.comp_apply,c]
      using hNativeDerivative.symm.trans (hFunctionDerivative.trans hCoreDerivative)
  have hUValue : sphereSobolevCoefficientL (3/2 : ℝ) k (U y) = v :=
    sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (3/2 : ℝ) F y k
  have hRot (a b : Fin 3) : sphereSobolevCoefficientL (1/2 : ℝ) k
      (sphereSobolevRotationL (3/2 : ℝ) a b (U y)) = harmonicSphereRotation k a b v := by
    have hIndex := congrArg (fun t : ℝ => sphereSobolevCoefficientL t k
      (sphereSobolevRotationL (3/2 : ℝ) a b (U y)))
      (show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num)
    exact hIndex.symm.trans
      ((sphereSobolevCoefficientL_rotation (3/2 : ℝ) a b k (U y)).trans
        (congrArg (harmonicSphereRotation k a b) hUValue))
  have hHorizontal : sphereSobolevCoefficientL (1/2 : ℝ) k
      (referenceHighHorizontalAction g L q U y i) =
      c (fderiv ℝ F.val y X) + (1/2 : ℝ) •
        ∑ a : Fin 3, ∑ b : Fin 3, Gamma a b • harmonicSphereRotation k a b v := by
    simp (config := { instances := true }) only
      [referenceHighHorizontalAction, referenceHighHorizontalAngularL,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
        map_add, map_smul, map_sum, sphereSobolevCoefficientL_inclusion, hBase, hRot, Gamma, X]
  have hCoreHorizontal : c ((coreReferenceHorizontal hO hD g hg L q i F).val y) =
      c (fderiv ℝ F.val y X) + (1/2 : ℝ) •
        ∑ a : Fin 3, ∑ b : Fin 3, Gamma a b • harmonicSphereRotation k a b v := by
    have h := congrArg c (coreReferenceHorizontal_apply hO hD g hg L q i F y)
    simpa (config := { instances := true }) only
      [coreFrameHorizontalAction, map_add, map_smul, map_sum, coreRotation,
        coreBlockOperator_coordinate, c, X, Gamma, v] using h
  exact hHorizontal.trans (hCoreHorizontal.symm.trans
    (sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (1/2 : ℝ)
      (coreReferenceHorizontal hO hD g hg L q i F) y k).symm)

/-- The exact Half norm of the raw finite-input horizontal action is an original
profile-energy term, rather than an estimate of a Hi spatial derivative. -/
lemma inv_beta_mul_sum_norm_referenceHighHorizontalAction_sq_le_referenceProfileEnergy
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q beta : ℝ) (hb : 0 ≤ beta)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    beta⁻¹ * (∑ i : Fin 3,
      ‖referenceHighHorizontalAction g L q
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) x i‖^2) ≤
      finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x := by
  have hHalf : (∑ i : Fin 3,
      ‖referenceHighHorizontalAction g L q (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) x i‖^2) =
      ∑ i : Fin 3, ‖(coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (coreReferenceHorizontal hO hD g hg L q i F)).val x‖^2 := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [referenceHighHorizontalAction_finiteCoreSobolevLift hO hD g hg L q F x i,
      norm_finiteCoreSobolevLift hO hD (1/2 : ℝ)]
  rw [hHalf]
  have hHorizontal : 0 ≤ ∑ i : Fin 3, ‖(coreReferenceHorizontal hO hD g hg L q i F).val x‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hOne : 0 ≤ beta^2 * ‖(coreWeightOperator hO hD (besselWeight 1) F).val x‖^2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hThreeHalf : 0 ≤ beta * ‖(coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F).val x‖^2 :=
    mul_nonneg hb (sq_nonneg _)
  unfold finiteCoreReferenceProfileEnergy SectionFiveErrorForms.sourceNormSquareIntegrand
  linarith only [hHorizontal, hOne, hThreeHalf]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic

/-- The genuine forward Half-to-zero inclusion and inverse zero-order isometry
contract the full Half input norm in the original spherical L2 space. -/
lemma norm_sphereSobolevHalfToSphereL2L_apply_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (v : SphereSobolev (1/2 : ℝ)) :
    ‖sphereSobolevHalfToSphereL2L hO hD v‖ ≤ ‖v‖ := by
  change ‖(sphereSobolevZeroEquiv hO hD).symm
    (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) v)‖ ≤ ‖v‖
  rw [(sphereSobolevZeroEquiv hO hD).symm.norm_map]
  exact ((sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)).le_opNorm v).trans
    (mul_le_of_le_one_left (norm_nonneg v)
      (norm_sphereSobolevInclusionL_le (1/2 : ℝ) 0 (by norm_num)))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
