import Calderon.SphereSobolevInclusion

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph

/-- The canonical half-order Sobolev inclusion into the sphere L2 space. -/
def sphereSobolevHalfToL2L
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereL2 :=
  (sphereSobolevZeroEquiv hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num))

/-- The named map is exactly the original inverse-zero-equivalence composition. -/
theorem sphereSobolevHalfToL2L_def
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    sphereSobolevHalfToL2L hO hD =
      (sphereSobolevZeroEquiv hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)) := rfl

end OAI.AnisotropicCalderon.SphereHarmonic
