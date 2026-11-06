import Calderon.ActualLowerUSLowerWordAdjoints

/-! Author-support GPT-6.1 Sol. Before-code ../gained-jq-upfront.md.
Support preservation for the genuine finite pretests in quadratic JQ.
Separate new source preserves earlier frozen source bytes. No compilation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hF : SphereFischerInner)

lemma finiteCoreSupportPreserving_lowerCoreAngularGenerator
    (i : LowerCoreAngularGeneratorIndex) :
    FiniteCoreSupportPreserving hO hD (lowerCoreAngularGenerator hO hD hF i) := by
  apply finiteCoreSupportPreserving_of_pointwise_adjoint hO hD _
    (lowerCoreAngularGeneratorAdjoint hO hD hF i)
  intro F G x
  exact (hasCoreAngularFirstOrderBounds_lowerCoreAngularGenerator hO hD hF i x).2.1 F G

lemma finiteCoreSupportPreserving_lowerCoreAngularGeneratorAdjoint
    (i : LowerCoreAngularGeneratorIndex) :
    FiniteCoreSupportPreserving hO hD (lowerCoreAngularGeneratorAdjoint hO hD hF i) := by
  apply finiteCoreSupportPreserving_of_pointwise_adjoint hO hD _
    (lowerCoreAngularGenerator hO hD hF i)
  intro F G x
  calc
    _ = ⟪G.val x,(lowerCoreAngularGeneratorAdjoint hO hD hF i F).val x⟫_ℝ :=
      real_inner_comm _ _
    _ = ⟪(lowerCoreAngularGenerator hO hD hF i G).val x,F.val x⟫_ℝ :=
      ((hasCoreAngularFirstOrderBounds_lowerCoreAngularGenerator hO hD hF i x).2.1 G F).symm
    _ = _ := real_inner_comm _ _

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints
