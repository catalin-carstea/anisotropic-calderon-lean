import Calderon.CoerciveFunctionalInverseEquality

set_option autoImplicit false
noncomputable section
open scoped ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

theorem contDiffAt_functionalInverse_of_coercive
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (A : E → V →L[ℝ] StrongDual ℝ V) (p : E)
    (hA : ContDiffAt ℝ ∞ A p) (hc : IsCoercive (A p)) :
    ContDiffAt ℝ ∞ (fun t => functionalInverse (A t)) p := by
  have hOp : ContDiffAt ℝ ∞
      (fun t => InnerProductSpace.continuousLinearMapOfBilin (A t)) p :=
    contDiffAt_const.clm_comp hA
  have he : (hc.continuousLinearEquivOfBilin : V →L[ℝ] V) =
      InnerProductSpace.continuousLinearMapOfBilin (A p) := rfl
  have hi := contDiffAt_map_inverse (n := ∞)
    hc.continuousLinearEquivOfBilin
  rw [he] at hi
  let D : StrongDual ℝ V →L[ℝ] V :=
    (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap
  change ContDiffAt ℝ ∞
    (fun t => (InnerProductSpace.continuousLinearMapOfBilin (A t)).inverse.comp D) p
  exact (hi.comp p hOp).clm_comp (contDiffAt_const (c := D))

theorem contDiff_weakDirichletRestriction
    {E U V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E → U →L[ℝ] StrongDual ℝ V) (J : V →L[ℝ] U)
    (hR : ContDiff ℝ ∞ R) :
    ContDiff ℝ ∞ (fun t => (R t).comp J) :=
  hR.clm_comp (contDiff_const (c := J))

theorem weakLift_formula_eq_inverse
    {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : V →L[ℝ] StrongDual ℝ V) (R : U →L[ℝ] StrongDual ℝ V)
    (J : V →L[ℝ] U) (P : X →L[ℝ] U) (hA : IsCoercive A) :
    ((ContinuousLinearMap.id ℝ U) - J.comp ((functionalInverse A).comp R)).comp P =
      ((ContinuousLinearMap.id ℝ U) - J.comp (A.inverse.comp R)).comp P := by
  have he : A.inverse = functionalInverse A :=
    (isInvertible_and_inverse_eq_functionalInverse A hA).2
  exact congrArg (fun G : StrongDual ℝ V →L[ℝ] V =>
    ((ContinuousLinearMap.id ℝ U) - J.comp (G.comp R)).comp P) he.symm

theorem contDiffAt_weakLift_formula
    {E U V X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : E → V →L[ℝ] StrongDual ℝ V) (R : E → U →L[ℝ] StrongDual ℝ V)
    (J : V →L[ℝ] U) (P : X →L[ℝ] U) (p : E)
    (hA : ContDiffAt ℝ ∞ A p) (hR : ContDiffAt ℝ ∞ R p) (hc : IsCoercive (A p)) :
    ContDiffAt ℝ ∞ (fun t =>
      ((ContinuousLinearMap.id ℝ U) - J.comp ((functionalInverse (A t)).comp (R t))).comp P) p := by
  have hI := contDiffAt_functionalInverse_of_coercive A p hA hc
  exact ((contDiffAt_const (c := ContinuousLinearMap.id ℝ U)).sub
    ((contDiffAt_const (c := J)).clm_comp (hI.clm_comp hR))).clm_comp
      (contDiffAt_const (c := P))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_functionalInverse_of_coercive
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_weakDirichletRestriction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.weakLift_formula_eq_inverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_weakLift_formula
