import Calderon.SphereSobolevCompletion

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
FINITE-ADJOINT-PRODUCT-ASSEMBLY-EXPANSION-v001.md. Existing partial sum as its literal finite CLM sum. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic

def sphereSobolevPartialSumL (s : ℝ) (n : ℕ) : SphereSobolev s →L[ℝ] SphereSobolev s :=
  ∑ k ∈ Finset.range n, (sphereSobolevSingleL s k).comp (sphereSobolevCoefficientL s k)

lemma sphereSobolevPartialSumL_apply (s : ℝ) (n : ℕ) (f : SphereSobolev s) :
    sphereSobolevPartialSumL s n f = sphereSobolevPartialSum s n f := by
  simp only [sphereSobolevPartialSumL,sphereSobolevPartialSum,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevPartialSumL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevPartialSumL_apply
