import Calderon.PhysicalDegreeCasimirScalarFunctionalsCore
import Calderon.PhysicalDegreeAdjointScalarOuterEvaluation
import Calderon.PhysicalDegreeAdjointScalarTermEvaluation
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic
/-! Original final1 is assembled from separately computed actual values, without unfolding
its original CLM definition. -/
lemma degreeAdjointScalarL_apply
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (ij : Fin 3 × Fin 3) (f g : SphereSobolev 1) (x : PhysicalDegreeCasimirData) :
    degreeAdjointScalarL hO hD ij f g x =
      ⟪(sphereSobolevZeroEquiv hO hD).symm (x.2.1 ij f),
        (sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) g)⟫_ℝ -
      ⟪(sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) f),
        (sphereSobolevZeroEquiv hO hD).symm (x.2.2 ij g)⟫_ℝ := by
  exact (degreeAdjointScalarL_apply_outer_sub hO hD ij f g x).trans
    (congrArg₂ (fun a b : ℝ => a-b)
      (degreePrimalPhysicalScalarL_apply hO hD ij f
        ((sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) g)) x)
      (degreeAdjointScalarTerm_apply hO hD ij f g x))

#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeAdjointScalarL_apply
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
