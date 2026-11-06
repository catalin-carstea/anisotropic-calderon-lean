import Calderon.InvertibleFunctionalInverseEquality

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-! Upfront expansion: EXPANSION-native-coefficient-weak-half-lift-factoring-repair-v001.json. -/

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

def weakAffineLiftAssembly (J : V →L[ℝ] U) (I : StrongDual ℝ V →L[ℝ] V)
    (R : U →L[ℝ] StrongDual ℝ V) (P : X →L[ℝ] U) : X →L[ℝ] U :=
  ((ContinuousLinearMap.id ℝ U)-J.comp (I.comp R)).comp P

lemma weakAffineLiftAssembly_apply (J : V →L[ℝ] U) (I : StrongDual ℝ V →L[ℝ] V)
    (R : U →L[ℝ] StrongDual ℝ V) (P : X →L[ℝ] U) (f : X) :
    weakAffineLiftAssembly J I R P f = P f-J (I (R (P f))) := rfl

lemma weakAffineLiftAssembly_kernel (J : V →L[ℝ] U) (I : StrongDual ℝ V →L[ℝ] V)
    (R : U →L[ℝ] StrongDual ℝ V) (P : X →L[ℝ] U)
    (hcancel : ∀ (ell : StrongDual ℝ V) (v : V), R (J (I ell)) v = ell v) (f : X) (v : V) :
    R (weakAffineLiftAssembly J I R P f) v = 0 := by
  rw [weakAffineLiftAssembly_apply]
  have hs := congrArg (fun ell : StrongDual ℝ V => ell v) (map_sub R (P f) (J (I (R (P f)))))
  exact hs.trans ((congrArg (fun t : ℝ => R (P f) v-t) (hcancel (R (P f)) v)).trans (sub_self _))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.weakAffineLiftAssembly
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.weakAffineLiftAssembly_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.weakAffineLiftAssembly_kernel
