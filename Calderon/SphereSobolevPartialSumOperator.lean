import Calderon.SphereSobolevCompletion

/-! The partial sum as its literal finite sum of continuous linear maps. -/
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
