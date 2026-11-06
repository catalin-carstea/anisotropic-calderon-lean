import TauCeti.Analysis.InnerProductSpace.LaxMilgram

/-! EXPANSION.json precedes the actual abstract inverse-zero identity. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource

lemma solutionOfFunctional_zero {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (A : V →L[ℝ] V →L[ℝ] ℝ) (hA : IsCoercive A) :
    hA.solutionOfFunctional (0 : StrongDual ℝ V) = 0 := by
  simp only [IsCoercive.solutionOfFunctional,IsCoercive.solutionOfInner,map_zero]

end OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
#print axioms OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource.solutionOfFunctional_zero
