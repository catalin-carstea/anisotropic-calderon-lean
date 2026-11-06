import TauCeti.Analysis.InnerProductSpace.LaxMilgram
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
lemma continuous_solutionOfFunctional {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] (A : V →L[ℝ] V →L[ℝ] ℝ)
    (hA : IsCoercive A) : Continuous (fun ell : StrongDual ℝ V => hA.solutionOfFunctional ell) := by
  change Continuous (fun ell : StrongDual ℝ V =>
    hA.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ V).symm ell))
  exact hA.continuousLinearEquivOfBilin.symm.continuous.comp
    (InnerProductSpace.toDual ℝ V).symm.continuous


end OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
#print axioms OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource.continuous_solutionOfFunctional
