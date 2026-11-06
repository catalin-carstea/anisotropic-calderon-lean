import Calderon.ActualAngularMixedEndpointPrimitives
import Calderon.ActualNativeMovingAdjointFiniteJ
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
/-- Actual full-output angular coordinate transpose, from the checked cross adjunction. -/
theorem actual_angular_coordinate_transpose_pairing
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i : Fin 3) (u : Hi) (v : Half) :
    PP (IH u) (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i v) =
      PP v (JL (loweringHigh hF hO hD i u)) := by
  change PP (IH u) (raisingLow hF hO hD i v) = _
  exact (v017_aA2 hF hO hD i u v).symm.trans
    (v016_pairing_inclusion_symm (loweringHigh hF hO hD i u) v)
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.actual_angular_coordinate_transpose_pairing
