import Calderon.SphereSobolevInclusion
import Calderon.PositiveSpectralCore

set_option autoImplicit false
noncomputable section
open Set MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph

/-- The literal constant-one sphere function as a degree-zero Sobolev single. -/
def sphereSobolevConstantOne (s : ℝ) : SphereSobolev s :=
  sphereSobolevSingleL s 0
    ⟨polynomialSphereL2 (C 1), polynomialSphereL2_mem 0 (C 1) (C_harmonicHomogeneous 1)⟩

lemma sphereSobolevInclusionL_constantOne (s t : ℝ) (hts : t ≤ s) :
    sphereSobolevInclusionL s t hts (sphereSobolevConstantOne s) =
      sphereSobolevConstantOne t := by
  exact sphereSobolevInclusionL_single s t hts 0
    ⟨polynomialSphereL2 (C 1), polynomialSphereL2_mem 0 (C 1) (C_harmonicHomogeneous 1)⟩

lemma sphereSobolevZeroEquiv_symm_constantOne
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    (sphereSobolevZeroEquiv hO hD).symm (sphereSobolevConstantOne 0) =
      polynomialSphereL2 (C 1) := by
  apply (sphereSobolevZeroEquiv hO hD).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change sphereSobolevSingleL 0 0
    ⟨polynomialSphereL2 (C 1), polynomialSphereL2_mem 0 (C 1) (C_harmonicHomogeneous 1)⟩ =
    sphereHarmonicDecomposition hO hD (polynomialSphereL2 (C 1))
  rw [sphereHarmonicDecomposition_subtype hO hD 0
    (⟨polynomialSphereL2 (C 1), polynomialSphereL2_mem 0 (C 1)
      (C_harmonicHomogeneous 1)⟩ : harmonicSphereSubspace 0)]
  simp [sphereSobolevSingleL,besselWeight_zero_order]

lemma sphereMean_sphereSobolevConstantOne
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    sphereMean ((sphereSobolevZeroEquiv hO hD).symm (sphereSobolevConstantOne 0)) = 1 := by
  rw [sphereSobolevZeroEquiv_symm_constantOne]
  exact sphereMean_constant_one

end OAI.AnisotropicCalderon.SphereHarmonic
