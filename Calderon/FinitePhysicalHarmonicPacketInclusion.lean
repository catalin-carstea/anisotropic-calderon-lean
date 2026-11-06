import Calderon.FinitePhysicalHarmonicPacketEnergy
import Calderon.FiniteAllNineCasimirPairingEstimate

set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.RotationCasimirEstimate
open SphereHarmonic SmoothSphereRotationProjection

lemma zeroEquiv_symm_inclusion_one_zero_finite_packet
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : Finset ℕ) (u : ∀ k, harmonicSphereSubspace k) :
    (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL 1 0 (by norm_num)
        (∑ k ∈ s, sphereSobolevSingleL 1 k (u k))) =
      ∑ k ∈ s, (u k : SphereL2) := by
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [sphereSobolevInclusionL_single]
  exact (congrArg (sphereSobolevZeroEquiv hO hD).symm
    (sphereSobolevZeroEquiv_harmonic_subtype hO hD k (u k))).symm.trans
      ((sphereSobolevZeroEquiv hO hD).symm_apply_apply (u k : SphereL2))

#print axioms OAI.AnisotropicCalderon.RotationCasimirEstimate.zeroEquiv_symm_inclusion_one_zero_finite_packet
end OAI.AnisotropicCalderon.RotationCasimirEstimate
