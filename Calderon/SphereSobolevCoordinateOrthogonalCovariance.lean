import Calderon.SphereCoordinateMultiplierOrthogonalCovariance
import Calderon.SphereSobolevZeroOrthogonalPullback
import Calderon.SphereSobolevCoordinateInclusion

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily

lemma sphereSobolevInclusionL_orthogonalPullback_apply
    (s t : ℝ) (hts : t ≤ s) (e : R3 ≃ₗᵢ[ℝ] R3) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hts (sphereSobolevOrthogonalPullbackL s e u) =
      sphereSobolevOrthogonalPullbackL t e (sphereSobolevInclusionL s t hts u) :=
  congrArg (fun A : SphereSobolev s →L[ℝ] SphereSobolev t => A u)
    (sphereSobolevInclusionL_orthogonalPullback s t hts e)

lemma sphereSobolevOrthogonalPullback_coordinateMul
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (hs : 0 ≤ s) (e : R3 ≃ₗᵢ[ℝ] R3) (i : Fin 3) (u : SphereSobolev s) :
    sphereSobolevOrthogonalPullbackL s e
      (sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single i 1) u) =
      ∑ j : Fin 3, (e (EuclideanSpace.single j 1)) i •
        sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single j 1)
          (sphereSobolevOrthogonalPullbackL s e u) := by
  let I : SphereSobolev s →L[ℝ] SphereSobolev 0 := sphereSobolevInclusionL s 0 hs
  let Z := sphereSobolevZeroEquiv hO hD
  let v : SphereL2 := Z.symm (I u)
  have hu : I u = Z v := (Z.apply_symm_apply (I u)).symm
  have hRu : I (sphereSobolevOrthogonalPullbackL s e u) = Z (sphereL2OrthogonalPullback e v) := by
    calc
      _ = sphereSobolevOrthogonalPullbackL 0 e (I u) :=
        sphereSobolevInclusionL_orthogonalPullback_apply s 0 hs e u
      _ = sphereSobolevOrthogonalPullbackL 0 e (Z v) :=
        congrArg (sphereSobolevOrthogonalPullbackL 0 e) hu
      _ = _ := (sphereSobolevZeroEquiv_orthogonalPullback hO hD e v).symm
  have hM : I (sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single i 1) u) =
      Z (sphereCoordinateMulL i v) := by
    simpa only [sphereLinearCoordinateMulL_single] using
      sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv hF hO hD s hs
        (EuclideanSpace.single i 1) u v hu
  have hMR (j : Fin 3) : I (sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single j 1)
      (sphereSobolevOrthogonalPullbackL s e u)) =
        Z (sphereCoordinateMulL j (sphereL2OrthogonalPullback e v)) := by
    simpa only [sphereLinearCoordinateMulL_single] using
      sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv hF hO hD s hs
        (EuclideanSpace.single j 1) (sphereSobolevOrthogonalPullbackL s e u)
        (sphereL2OrthogonalPullback e v) hRu
  apply sphereSobolevInclusionL_injective s 0 hs
  change I (sphereSobolevOrthogonalPullbackL s e
      (sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single i 1) u)) = _
  calc
    _ = sphereSobolevOrthogonalPullbackL 0 e
        (I (sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single i 1) u)) :=
      sphereSobolevInclusionL_orthogonalPullback_apply s 0 hs e _
    _ = sphereSobolevOrthogonalPullbackL 0 e (Z (sphereCoordinateMulL i v)) :=
      congrArg (sphereSobolevOrthogonalPullbackL 0 e) hM
    _ = Z (sphereL2OrthogonalPullback e (sphereCoordinateMulL i v)) :=
      (sphereSobolevZeroEquiv_orthogonalPullback hO hD e _).symm
    _ = Z (∑ j : Fin 3, (e (EuclideanSpace.single j 1)) i •
        sphereCoordinateMulL j (sphereL2OrthogonalPullback e v)) :=
      congrArg Z (sphereL2OrthogonalPullback_coordinateMul e i v)
    _ = ∑ j : Fin 3, (e (EuclideanSpace.single j 1)) i •
        Z (sphereCoordinateMulL j (sphereL2OrthogonalPullback e v)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact map_smul Z _ _
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul]
      exact congrArg ((e (EuclideanSpace.single j 1)) i • ·) (hMR j).symm

end OAI.AnisotropicCalderon.SphereHarmonic
