import Calderon.SphereSobolevPairing
import Calderon.SphereSobolevInclusion

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereSobolevDualPairing_threeHalf_cross_inclusion
    (u : SphereSobolev (3 / 2 : ℝ)) (w : SphereSobolev (1 / 2 : ℝ)) :
    sphereSobolevDualPairing (3 / 2 : ℝ) u
        (sphereSobolevInclusionL (1 / 2 : ℝ) (-(3 / 2 : ℝ)) (by norm_num) w) =
      sphereSobolevDualPairing (-(1 / 2 : ℝ))
        (sphereSobolevInclusionL (3 / 2 : ℝ) (-(1 / 2 : ℝ)) (by norm_num) u) w := by
  rw [sphereSobolevDualPairing_eq_tsum, sphereSobolevDualPairing_eq_tsum]
  apply tsum_congr
  intro k
  simp only [sphereSobolevCoefficientL_inclusion]
  have hCoeff (z : SphereSobolev (1/2 : ℝ)) :
      sphereSobolevCoefficientL (-(-(1/2 : ℝ))) k z =
        sphereSobolevCoefficientL (1/2 : ℝ) k z :=
    congrArg (fun t : ℝ => sphereSobolevCoefficientL t k z) (neg_neg (1/2 : ℝ))
  exact congrArg (fun z : harmonicSphereSubspace k =>
    ⟪sphereSobolevCoefficientL (3/2 : ℝ) k u, z⟫_ℝ) (hCoeff w).symm

lemma sphereSobolevDualPairing_half_cross_inclusion_comm
    (v : SphereSobolev (3 / 2 : ℝ)) (w : SphereSobolev (1 / 2 : ℝ)) :
    sphereSobolevDualPairing (-(1 / 2 : ℝ))
        (sphereSobolevInclusionL (3 / 2 : ℝ) (-(1 / 2 : ℝ)) (by norm_num) v) w =
      sphereSobolevDualPairing (-(1 / 2 : ℝ))
        (sphereSobolevInclusionL (1 / 2 : ℝ) (-(1 / 2 : ℝ)) (by norm_num) w)
        (sphereSobolevInclusionL (3 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) v) := by
  rw [sphereSobolevDualPairing_eq_tsum, sphereSobolevDualPairing_eq_tsum]
  apply tsum_congr
  intro k
  have hCoeff (z : SphereSobolev (1/2 : ℝ)) :
      sphereSobolevCoefficientL (-(-(1/2 : ℝ))) k z =
        sphereSobolevCoefficientL (1/2 : ℝ) k z :=
    congrArg (fun t : ℝ => sphereSobolevCoefficientL t k z) (neg_neg (1/2 : ℝ))
  have hA : sphereSobolevCoefficientL (-(1/2 : ℝ)) k
      (sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v) =
      sphereSobolevCoefficientL (3/2 : ℝ) k v :=
    sphereSobolevCoefficientL_inclusion (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v k
  have hB : sphereSobolevCoefficientL (-(-(1/2 : ℝ))) k w =
      sphereSobolevCoefficientL (1/2 : ℝ) k w := hCoeff w
  have hC : sphereSobolevCoefficientL (-(1/2 : ℝ)) k
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) w) =
      sphereSobolevCoefficientL (1/2 : ℝ) k w :=
    sphereSobolevCoefficientL_inclusion (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) w k
  have hD : sphereSobolevCoefficientL (-(-(1/2 : ℝ))) k
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v) =
      sphereSobolevCoefficientL (3/2 : ℝ) k v :=
    (hCoeff (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v)).trans
      (sphereSobolevCoefficientL_inclusion (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v k)
  exact (congrArg₂ (fun (a b : harmonicSphereSubspace k) => ⟪a, b⟫_ℝ) hA hB).trans
    ((real_inner_comm (sphereSobolevCoefficientL (1/2 : ℝ) k w)
      (sphereSobolevCoefficientL (3/2 : ℝ) k v)).trans
        (congrArg₂ (fun (a b : harmonicSphereSubspace k) => ⟪a, b⟫_ℝ) hC hD).symm)

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_threeHalf_cross_inclusion
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_half_cross_inclusion_comm
