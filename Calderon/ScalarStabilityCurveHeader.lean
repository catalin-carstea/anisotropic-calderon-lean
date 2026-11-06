import Calderon.ParametricCoerciveInverse
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Filter
open scoped Topology
namespace OAI.AnisotropicCalderon.DirichletFamily

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {I : Type*}

def scalarEnergyCurveLimitPredicate (l : Filter I)
    (B : I → V →L[ℝ] StrongDual ℝ V) (C : V →L[ℝ] StrongDual ℝ V) : Prop :=
  Tendsto B l (𝓝 C)

def scalarForcingCurveLimitPredicate (l : Filter I)
    (ell : I → StrongDual ℝ V) (ell0 : StrongDual ℝ V) : Prop :=
  Tendsto ell l (𝓝 ell0)

end OAI.AnisotropicCalderon.DirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.scalarEnergyCurveLimitPredicate
#print axioms OAI.AnisotropicCalderon.DirichletFamily.scalarForcingCurveLimitPredicate
