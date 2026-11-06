import Calderon.SharpRadialHarmonicCoefficientCore
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevSingleL sphereSobolevCoefficientL sphereSobolevZeroEquiv
/-! Full upfront: EXPANSION-v002.json. Typed constructor diagnostic only. -/
lemma sphereSobolev_clm_finite_packet_apply_diagnostic
    (T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (s : Finset ℕ) (u : ∀ k, harmonicSphereSubspace k) :
    T (∑ k ∈ s, sphereSobolevSingleL 1 k (u k)) =
      ∑ k ∈ s, T (sphereSobolevSingleL 1 k (u k)) := by
  exact map_sum T (fun k => sphereSobolevSingleL 1 k (u k)) s
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolev_clm_finite_packet_apply_diagnostic
end OAI.AnisotropicCalderon.SphereHarmonic
