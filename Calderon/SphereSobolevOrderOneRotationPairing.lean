import Calderon.SphereSobolevOrderOneRotation
import Calderon.ActualNormalizedSphereRotation

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotationProjection ActualNormalizedSphereRotation SpectralCoreRegularity

/-! The zero equivalence decodes the H1 inclusion and R1 into probability-L2 vectors.
Their rotation graph memberships imply physical skew adjunction, including degree zero. -/

lemma inner_sphereSobolevRotationL_one_zeroEquiv_skew
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) (u v : SphereSobolev 1) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm (sphereSobolevRotationL 1 i j u),
      (sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL 1 0 (by norm_num) v)⟫_ℝ =
    -⟪(sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL 1 0 (by norm_num) u),
      (sphereSobolevZeroEquiv hO hD).symm (sphereSobolevRotationL 1 i j v)⟫_ℝ := by
  let Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  let I : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL 1 0 (by norm_num)
  let R : SphereSobolev 1 →L[ℝ] SphereSobolev 0 := sphereSobolevRotationL 1 i j
  have hDecode (k : ℕ) (y : SphereSobolev 0) :
      sphereHarmonicCoordinate hO hD k (Z.symm y) = sphereSobolevCoefficientL 0 k y := by
    exact (sphereSobolevCoefficientL_zeroEquiv hO hD k (Z.symm y)).symm.trans
      (congrArg (sphereSobolevCoefficientL 0 k) (Z.apply_symm_apply y))
  have hGraph (x : SphereSobolev 1) :
      (Z.symm (I x),Z.symm (R x)) ∈ sphereRotationGraph hO hD i j := by
    intro k
    have hRotation : sphereSobolevCoefficientL 0 k (R x) =
        harmonicSphereRotation k i j (sphereSobolevCoefficientL 1 k x) := by
      simpa only [sphereSobolevCoefficientL,sub_self] using
        sphereSobolevCoefficientL_rotation 1 i j k x
    calc
      sphereHarmonicCoordinate hO hD k (Z.symm (R x)) =
          sphereSobolevCoefficientL 0 k (R x) := hDecode k (R x)
      _ = harmonicSphereRotation k i j (sphereSobolevCoefficientL 1 k x) := hRotation
      _ = harmonicSphereRotation k i j (sphereSobolevCoefficientL 0 k (I x)) :=
        congrArg (harmonicSphereRotation k i j)
          (sphereSobolevCoefficientL_inclusion 1 0 (by norm_num) x k).symm
      _ = harmonicSphereRotation k i j
          (sphereHarmonicCoordinate hO hD k (Z.symm (I x))) :=
        congrArg (harmonicSphereRotation k i j) (hDecode k (I x)).symm
  exact sphereRotationGraph_inner_skew hO hD i j
    (Z.symm (I u)) (Z.symm (R u)) (Z.symm (I v)) (Z.symm (R v))
    (hGraph u) (hGraph v)

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.inner_sphereSobolevRotationL_one_zeroEquiv_skew
