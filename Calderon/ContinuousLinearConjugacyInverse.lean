import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! Expanded first in EXPANSION-actual-rotation-normal-multiplier-inverse-author-v001.json. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma isInvertible_of_continuousLinear_conjugacy
    (A B T S : V →L[ℝ] V) (hTS : ∀ x, T (S x) = x) (hST : ∀ x, S (T x) = x)
    (hBT : ∀ x, B (T x) = T (A x)) (hi : A.IsInvertible) : B.IsInvertible := by
  have hT : T.IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := S)
    · exact ContinuousLinearMap.ext hTS
    · exact ContinuousLinearMap.ext hST
  have hS : S.IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := T)
    · exact ContinuousLinearMap.ext hST
    · exact ContinuousLinearMap.ext hTS
  have hB : B = T.comp (A.comp S) := by
    apply ContinuousLinearMap.ext
    intro x
    calc B x = B (T (S x)) := congrArg B (hTS x).symm
         _ = T (A (S x)) := hBT (S x)
  rw [hB]
  exact hT.comp (hi.comp hS)

lemma inverse_apply_of_continuousLinear_conjugacy
    (A B T S : V →L[ℝ] V) (hTS : ∀ x, T (S x) = x) (hST : ∀ x, S (T x) = x)
    (hBT : ∀ x, B (T x) = T (A x)) (hi : A.IsInvertible) (x : V) :
    B.inverse (T x) = T (A.inverse x) := by
  have hB := isInvertible_of_continuousLinear_conjugacy A B T S hTS hST hBT hi
  apply hB.inverse_apply_eq.mpr
  rw [hBT, hi.self_apply_inverse]

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.isInvertible_of_continuousLinear_conjugacy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.inverse_apply_of_continuousLinear_conjugacy
