import Calderon.NativeWeakHalfLiftTopologyAlgebra
import Calderon.InvertibleFunctionalInverseEquality

set_option autoImplicit false
noncomputable section
open scoped ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

theorem contDiffAt_functionalInverse_of_isInvertible
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (A : E → V →L[ℝ] StrongDual ℝ V) (p : E)
    (hA : ContDiffAt ℝ ∞ A p) (hi : (A p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t => functionalInverse (A t)) p := by
  simp only [functionalInverse_eq_inverse]
  exact hi.contDiffAt_map_inverse.comp p hA

theorem contDiffAt_weakLift_formula_of_isInvertible
    {E U V X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : E → V →L[ℝ] StrongDual ℝ V) (R : E → U →L[ℝ] StrongDual ℝ V)
    (J : V →L[ℝ] U) (P : X →L[ℝ] U) (p : E)
    (hA : ContDiffAt ℝ ∞ A p) (hR : ContDiffAt ℝ ∞ R p)
    (hi : (A p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t =>
      ((ContinuousLinearMap.id ℝ U) - J.comp ((functionalInverse (A t)).comp (R t))).comp P) p := by
  have hI := contDiffAt_functionalInverse_of_isInvertible A p hA hi
  exact ((contDiffAt_const (c := ContinuousLinearMap.id ℝ U)).sub
    ((contDiffAt_const (c := J)).clm_comp (hI.clm_comp hR))).clm_comp
      (contDiffAt_const (c := P))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_functionalInverse_of_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_weakLift_formula_of_isInvertible
