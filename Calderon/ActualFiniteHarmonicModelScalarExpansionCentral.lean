import Calderon.ActualFiniteHarmonicModelScalarExpansionClosure

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma scalarCentral_of_hasCoreScalarExpansionBound
    {ι : Type} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hT : ∀ i, ScalarCentral hO hD (T i))
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD T A x C) : ScalarCentral hO hD A := by
  obtain ⟨c,hc,he,_⟩ := hA
  rw [he]
  unfold coreScalarCombination
  apply scalarCentral_sum hO hD Finset.univ
  intro i _
  exact scalarCentral_mul hO hD _ _ (scalarCentral_coreScalar hO hD (c i) (hc i)) (hT i)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
