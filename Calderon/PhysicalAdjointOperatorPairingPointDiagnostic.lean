import Calderon.FinitePhysicalHarmonicPacketEnergy
set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.RotationCasimirEstimate
open SphereHarmonic
attribute [local irreducible] sphereSobolevSingleL sphereSobolevCoefficientL
  sphereSobolevZeroEquiv sphereSobolevInclusionL
/-! Full upfront: EXPANSION-v002.json. Exact physicaladjunction point application,
not a derivation of actualCsharp or of the selected paper balanced bound. -/
lemma physical_adjoint_operator_pairing_apply_diagnostic
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (P Q : Fin 3 × Fin 3 → (SphereSobolev 1 →L[ℝ] SphereSobolev 0))
    (hDual : ∀ ij, ∀ f h : SphereSobolev 1,
      ⟪(sphereSobolevZeroEquiv hO hD).symm (P ij f),
        (sphereSobolevZeroEquiv hO hD).symm
          (sphereSobolevInclusionL 1 0 (by norm_num) h)⟫_ℝ =
      ⟪(sphereSobolevZeroEquiv hO hD).symm
          (sphereSobolevInclusionL 1 0 (by norm_num) f),
        (sphereSobolevZeroEquiv hO hD).symm (Q ij h)⟫_ℝ)
    (ij : Fin 3 × Fin 3) (f h : SphereSobolev 1) :
      ⟪(sphereSobolevZeroEquiv hO hD).symm (P ij f),
        (sphereSobolevZeroEquiv hO hD).symm
          (sphereSobolevInclusionL 1 0 (by norm_num) h)⟫_ℝ =
      ⟪(sphereSobolevZeroEquiv hO hD).symm
          (sphereSobolevInclusionL 1 0 (by norm_num) f),
        (sphereSobolevZeroEquiv hO hD).symm (Q ij h)⟫_ℝ := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PHYSICAL_ADJOINT_POINT_ENTER"
    out.flush
  exact hDual ij f h
#print axioms OAI.AnisotropicCalderon.RotationCasimirEstimate.physical_adjoint_operator_pairing_apply_diagnostic
end OAI.AnisotropicCalderon.RotationCasimirEstimate
