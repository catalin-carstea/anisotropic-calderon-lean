import Calderon.SphereSobolevCoordinateMultiplier
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic
lemma sphereSobolevLinearCoordinateMulL_negative_half_notation_eq
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (d : R3) :
    sphereSobolevLinearCoordinateMulL hF hO hD (-1/2:ℝ) d =
      sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2:ℝ)) d := by
  unfold sphereSobolevLinearCoordinateMulL sphereSobolevRadialDriftAdjointL sphereSobolevRadialDriftL
  simp only [neg_div, neg_neg]
end OAI.AnisotropicCalderon.SphereHarmonic
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevLinearCoordinateMulL_negative_half_notation_eq
