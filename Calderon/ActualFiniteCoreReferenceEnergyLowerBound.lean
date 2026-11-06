import Calderon.ActualLowerSSelfFormation
import Calderon.ActualFiniteCoreSobolevRepresentation
import Calderon.SphereSobolevInclusion

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore DirichletFamily.DriftBootstrap

/-- The genuine three-half finite input controls the original spherical L2 norm,
by the exact zero-order isometry and contractive forward Sobolev inclusion. -/
lemma norm_finiteCore_eval_le_norm_threeHalf_lift
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ‖F.val x‖ ≤ ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F x‖ := by
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
  have hRep : I (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) =
      sphereSobolevZeroEquiv hO hD (F.val x) :=
    (finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F).2.2.2.1 x
  have hI : ‖I‖ ≤ 1 := norm_sphereSobolevInclusionL_le (3/2 : ℝ) 0 (by norm_num)
  calc
    ‖F.val x‖ = ‖sphereSobolevZeroEquiv hO hD (F.val x)‖ :=
      ((sphereSobolevZeroEquiv hO hD).norm_map _).symm
    _ = ‖I (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)‖ := congrArg norm hRep.symm
    _ ≤ ‖I‖ * ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F x‖ := I.le_opNorm _
    _ ≤ ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F x‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hI

/-- The original profile energy bounds beta times the original input norm,
with the coefficient derived from the actual input-space maps. -/
lemma beta_mul_norm_finiteCore_eval_sq_le_referenceProfileEnergy
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q beta : ℝ)
    (hb : 0 ≤ beta) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    beta * ‖F.val x‖^2 ≤ finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x := by
  have hNorm := norm_finiteCore_eval_le_norm_threeHalf_lift hO hD F x
  have hSquare : ‖F.val x‖^2 ≤ ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F x‖^2 := by
    nlinarith [norm_nonneg (F.val x), norm_nonneg (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)]
  have hEnergy := ActualLowerSSelfFormation.beta_mul_norm_higherSInput_sq_le_referenceProfileEnergy
    g L hg hO hD q beta hb F x
  change beta * ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F x‖^2 ≤ _ at hEnergy
  exact (mul_le_mul_of_nonneg_left hSquare hb).trans hEnergy

/-- A beta floor of one makes the original profile energy dominate the original
finite input norm, without an assumed norm-comparison constant. -/
lemma norm_finiteCore_eval_sq_le_referenceProfileEnergy
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q beta : ℝ)
    (hb : 1 ≤ beta) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ‖F.val x‖^2 ≤ finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x := by
  have hNorm := norm_finiteCore_eval_le_norm_threeHalf_lift hO hD F x
  have hSquare : ‖F.val x‖^2 ≤ ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F x‖^2 := by
    nlinarith [norm_nonneg (F.val x), norm_nonneg (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)]
  have hEnergy := ActualLowerSSelfFormation.norm_higherSInput_sq_le_referenceProfileEnergy
    g L hg hO hD q beta hb F x
  change ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F x‖^2 ≤ _ at hEnergy
  exact hSquare.trans hEnergy

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
