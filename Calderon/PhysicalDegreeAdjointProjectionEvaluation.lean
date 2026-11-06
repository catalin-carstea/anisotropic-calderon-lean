import Calderon.PhysicalDegreeCasimirAmbientData
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
/-! Full upfront EXPANSION-v001.json. Literal ORIGINAL adjoint projection value;
no zero-equivalence or inner-product unfolding is required. -/
lemma degreeAdjointProjectionL_apply
    (ij : Fin 3 × Fin 3) (x : PhysicalDegreeCasimirData) :
    degreeAdjointProjectionL ij x = x.2.2 ij := by
  simp only [degreeAdjointProjectionL,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd',ContinuousLinearMap.proj_apply]
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeAdjointProjectionL_apply
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
