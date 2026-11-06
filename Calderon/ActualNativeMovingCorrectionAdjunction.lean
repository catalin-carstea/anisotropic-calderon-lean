import Calderon.ActualNativeMovingAdjointCorrectionInclusion

/-! Actual Main M1 Products adjoint. Full nine-root before-code expansion and
exact original definitions were reviewed before authoring. No quantitative
Productsdag cap, finite-output assumption or intrinsic Half adjoint is used. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevZeroEquiv
  sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL
  sphereSobolevLinearCoordinateMulL referenceNativeMovingAdjointParametricCorrection

def referenceNativeMovingParametricCorrection
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L : ℝ)
    (s : ℝ) (z : (ℝ × R3) × (R3 →L[ℝ] ℝ)) (i : Fin 3) :
    SphereSobolev s →L[ℝ] SphereSobolev s :=
  (sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single i 1)).comp
    (sphereSobolevRadialDriftL hF hO hD s (referenceCenterDrift g L z.1.1 z.1.2)) +
  z.2 (conformalReferenceGramFrameOperatorJoint g L z.1 (coordinateVector i)) •
    sphereSobolevRadialDriftL hF hO hD s (referenceCenterDrift g L z.1.1 z.1.2)

lemma referenceNativeMovingParametricCorrection_inclusion
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L : ℝ)
    (s t : ℝ) (hts : t ≤ s) (z : (ℝ × R3) × (R3 →L[ℝ] ℝ))
    (i : Fin 3) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hts
      (referenceNativeMovingParametricCorrection hF hO hD g L s z i u) =
    referenceNativeMovingParametricCorrection hF hO hD g L t z i
      (sphereSobolevInclusionL s t hts u) := by
  let d := referenceCenterDrift g L z.1.1 z.1.2
  let c := z.2 (conformalReferenceGramFrameOperatorJoint g L z.1 (coordinateVector i))
  let I := sphereSobolevInclusionL s t hts
  let Ds := sphereSobolevRadialDriftL hF hO hD s d
  let Dt := sphereSobolevRadialDriftL hF hO hD t d
  let Ms := sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single i 1)
  let Mt := sphereSobolevLinearCoordinateMulL hF hO hD t (EuclideanSpace.single i 1)
  have hD1 : I (Ds u) = Dt (I u) :=
    sphereSobolevInclusionL_radialDrift hF hO hD s t hts d u
  have hM : I (Ms (Ds u)) = Mt (I (Ds u)) :=
    sphereSobolevInclusionL_linearCoordinateMul hF hO hD s t hts
      (EuclideanSpace.single i 1) (Ds u)
  have hValue := congrArg₂ (fun a b : SphereSobolev t => a+b)
    (hM.trans (congrArg Mt hD1))
    (congrArg (fun v : SphereSobolev t => c • v) hD1)
  simpa only [referenceNativeMovingParametricCorrection,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,map_add,map_smul,I,Ds,Dt,Ms,Mt,d,c] using hValue


lemma inner_zero_referenceNativeMovingParametricCorrection_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L : ℝ)
    (z : (ℝ × R3) × (R3 →L[ℝ] ℝ)) (i : Fin 3)
    (u v : SphereSobolev (1/2 : ℝ)) :
    ⟪sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) v,
      sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) z i u)⟫_ℝ =
    ⟪sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (referenceNativeMovingParametricCorrection hF hO hD g L (1/2 : ℝ) z i v),
      sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) u⟫_ℝ := by
  let J : Half →L[ℝ] Neg := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Z : Half →L[ℝ] SphereSobolev 0 := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Q : Half → Neg → ℝ := sphereSobolevDualPairing (1/2 : ℝ)
  let d := referenceCenterDrift g L z.1.1 z.1.2
  let c := z.2 (conformalReferenceGramFrameOperatorJoint g L z.1 (coordinateVector i))
  let D : Half →L[ℝ] Half := sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) d
  let Dn : Neg →L[ℝ] Neg := sphereSobolevRadialDriftL hF hO hD (-(1/2 : ℝ)) d
  let Ddag : Half →L[ℝ] Half := sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) d
  let M : Half →L[ℝ] Half := sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1)
  let Mn : Neg →L[ℝ] Neg := sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single i 1)
  have hInc (a b : Half) : Q a (J b) = ⟪Z a,Z b⟫_ℝ := by
    have hFlip : Q a (J b) = sphereSobolevDualPairing (-(1/2 : ℝ)) (J b) a := by
      change ⟪a,J b⟫_ℝ = ⟪J b,a⟫_ℝ
      exact real_inner_comm (J b) a
    exact hFlip.trans ((sphereSobolevDualPairing_inclusion_eq_inner_zero
      (1/2 : ℝ) (by norm_num) b a).trans (real_inner_comm (Z a) (Z b)))
  have hSym (a b : Half) : Q a (J b) = Q b (J a) :=
    (hInc a b).trans ((real_inner_comm (Z b) (Z a)).trans (hInc b a).symm)
  have hDriftPair (a b : Half) : ⟪Z a,Z (Ddag b)⟫_ℝ = ⟪Z (D a),Z b⟫_ℝ := by
    have hCompat : Dn (J a) = J (D a) :=
      (sphereSobolevInclusionL_radialDrift hF hO hD (1/2 : ℝ) (-(1/2 : ℝ))
        (by norm_num) d a).symm
    have hPair : Q (Ddag b) (J a) = Q b (Dn (J a)) :=
      sphereSobolevDualPairing_radialDriftAdjoint hF hO hD (1/2 : ℝ) d b (J a)
    exact (hInc a (Ddag b)).symm.trans ((hSym a (Ddag b)).trans
      (hPair.trans ((congrArg (Q b) hCompat).trans ((hSym b (D a)).trans (hInc (D a) b)))))
  have hM (a b : Half) : ⟪Z a,Z (M b)⟫_ℝ = ⟪Z (M a),Z b⟫_ℝ := by
    have hCompat : J (M b) = Mn (J b) :=
      sphereSobolevInclusionL_linearCoordinateMul hF hO hD (1/2 : ℝ) (-(1/2 : ℝ))
        (by norm_num) (EuclideanSpace.single i 1) b
    have hDual : Q a (Mn (J b)) = Q (M a) (J b) :=
      sphereSobolevDualPairing_linearCoordinate_half_duality hF hO hD
        (EuclideanSpace.single i 1) (J b) a
    exact (hInc a (M b)).symm.trans ((congrArg (Q a) hCompat).trans
      (hDual.trans (hInc (M a) b)))
  have hMain : ⟪Z v,Z (Ddag (M u)+c • Ddag u)⟫_ℝ =
      ⟪Z (M (D v)+c • D v),Z u⟫_ℝ := by
    simp only [map_add,map_smul,inner_add_right,inner_add_left,
      real_inner_smul_right,real_inner_smul_left]
    exact congrArg₂ (fun a b : ℝ => a+b) ((hDriftPair v (M u)).trans (hM (D v) u))
      (congrArg (fun a : ℝ => c*a) (hDriftPair v u))
  simpa only [referenceNativeMovingAdjointParametricCorrection,
    referenceNativeMovingParametricCorrection,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,Z,Ddag,D,M,d,c] using hMain


lemma contDiff_referenceNativeMovingParametricCorrection_joint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L s : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (referenceNativeMovingParametricCorrection hF hO hD g L s · i) := by
  letI : IsBoundedSMul ℝ (SphereSobolev s →L[ℝ] SphereSobolev s) :=
    @NormedSpace.toIsBoundedSMul ℝ (SphereSobolev s →L[ℝ] SphereSobolev s) Real.normedField
      (ContinuousLinearMap.toSeminormedAddCommGroup (E := SphereSobolev s)
        (F := SphereSobolev s) (σ₁₂ := RingHom.id ℝ))
      (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ) (E := SphereSobolev s)
        (F := SphereSobolev s) (σ₁₂ := RingHom.id ℝ))
  have hDrift : ContDiff ℝ ∞ (fun z : (ℝ × R3) × (R3 →L[ℝ] ℝ) =>
      sphereSobolevRadialDriftL hF hO hD s (referenceCenterDrift g L z.1.1 z.1.2)) :=
    (contDiff_reference_sphereSobolevRadialDriftL g hg L hF hO hD s).comp contDiff_fst
  have hFrame : ContDiff ℝ ∞ (fun z : (ℝ × R3) × (R3 →L[ℝ] ℝ) =>
      conformalReferenceGramFrameOperatorJoint g L z.1) :=
    (contDiff_conformalReferenceGramFrameOperatorJoint g hg L).comp contDiff_fst
  have hWeight : ContDiff ℝ ∞ (fun z : (ℝ × R3) × (R3 →L[ℝ] ℝ) =>
      z.2 (conformalReferenceGramFrameOperatorJoint g L z.1 (coordinateVector i))) :=
    contDiff_snd.clm_apply (hFrame.clm_apply contDiff_const)
  unfold referenceNativeMovingParametricCorrection
  exact (contDiff_const.clm_comp hDrift).add (hWeight.smul hDrift)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNativeMovingParametricCorrection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNativeMovingParametricCorrection_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.inner_zero_referenceNativeMovingParametricCorrection_adjoint
