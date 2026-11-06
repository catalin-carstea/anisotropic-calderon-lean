import Calderon.ContinuousLinearSectionSupport
import Calderon.RealNormedGroupProjectionData

/-! Before-source: actual-physical-full-allocation-author-oct16-v001/
EXPANSION-canonical-zero-decoding-section-support-v040.md. SAME canonical decoding map. -/
set_option autoImplicit false
noncomputable section
open Set
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic

lemma tsupport_sphereSobolevZeroEquiv_symm_clm_apply_subset
    {X : Type*} [TopologicalSpace X]
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (T : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (U : X → SphereSobolev 1) :
    tsupport (fun x => (sphereSobolevZeroEquiv hO hD).symm (T x (U x))) ⊆ tsupport U := by
  exact tsupport_clm_comp_apply_subset
    (X := X) (E := SphereSobolev 1) (F := SphereSobolev 0) (G := SphereL2)
    (sphereSobolevZeroEquiv hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap T U

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tsupport_sphereSobolevZeroEquiv_symm_clm_apply_subset
