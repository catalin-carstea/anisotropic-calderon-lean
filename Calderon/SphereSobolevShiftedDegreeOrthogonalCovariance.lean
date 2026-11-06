import Calderon.SphereSobolevShiftedPhysicalDegree
import Calderon.SphereSobolevOrthogonalPullback

/-! Exact decoded diagonal identity. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereSobolevShiftedDegreeL_orthogonalPullback_apply
    (s : ℝ) (e : R3 ≃ₗᵢ[ℝ] R3) (f : SphereSobolev s) :
    sphereSobolevShiftedDegreeL s (sphereSobolevOrthogonalPullbackL s e f) =
      sphereSobolevOrthogonalPullbackL (s-1) e (sphereSobolevShiftedDegreeL s f) := by
  apply sphereSobolev_ext (s-1)
  intro m
  calc
    _ = (m:ℝ) • sphereSobolevCoefficientL s m (sphereSobolevOrthogonalPullbackL s e f) :=
      sphereSobolevCoefficientL_shiftedDegree s m (sphereSobolevOrthogonalPullbackL s e f)
    _ = (m:ℝ) • harmonicSphereOrthogonalPullback e m (sphereSobolevCoefficientL s m f) :=
      congrArg (fun z : harmonicSphereSubspace m => (m:ℝ) • z)
        (sphereSobolevCoefficientL_orthogonalPullback s e f m)
    _ = harmonicSphereOrthogonalPullback e m ((m:ℝ) • sphereSobolevCoefficientL s m f) :=
      ((harmonicSphereOrthogonalPullback e m).map_smul _ _).symm
    _ = harmonicSphereOrthogonalPullback e m
        (sphereSobolevCoefficientL (s-1) m (sphereSobolevShiftedDegreeL s f)) :=
      congrArg (harmonicSphereOrthogonalPullback e m)
        (sphereSobolevCoefficientL_shiftedDegree s m f).symm
    _ = _ := (sphereSobolevCoefficientL_orthogonalPullback (s-1) e
      (sphereSobolevShiftedDegreeL s f) m).symm

end OAI.AnisotropicCalderon.SphereHarmonic
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevShiftedDegreeL_orthogonalPullback_apply
