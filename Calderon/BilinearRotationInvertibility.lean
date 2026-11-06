import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! Upfront expansion: EXPANSION-native-orthogonal-zero-energy-invertibility-author-v001.json. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma dualPrecomposition_isInvertible_of_inverse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T S : V →L[ℝ] V) (hST : ∀ x, S (T x) = x) (hTS : ∀ x, T (S x) = x) :
    ((ContinuousLinearMap.compL ℝ V V ℝ).flip T).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (ContinuousLinearMap.compL ℝ V V ℝ).flip S)
  · apply ContinuousLinearMap.ext
    intro ell
    apply ContinuousLinearMap.ext
    intro x
    change ell (S (T x)) = ell x
    rw [hST]
  · apply ContinuousLinearMap.ext
    intro ell
    apply ContinuousLinearMap.ext
    intro x
    change ell (T (S x)) = ell x
    rw [hTS]

lemma isInvertible_of_bilinear_rotation_covariance
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B : V →L[ℝ] V →L[ℝ] ℝ) (T S : V →L[ℝ] V)
    (hST : ∀ x, S (T x) = x) (hTS : ∀ x, T (S x) = x)
    (hcov : ∀ u v, B (T u) (T v) = A u v) (hi : A.IsInvertible) :
    B.IsInvertible := by
  have hS : S.IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := T)
    · apply ContinuousLinearMap.ext
      exact hST
    · apply ContinuousLinearMap.ext
      exact hTS
  have hP := dualPrecomposition_isInvertible_of_inverse S T hTS hST
  have hB : B = ((ContinuousLinearMap.compL ℝ V V ℝ).flip S).comp (A.comp S) := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change B u v = A (S u) (S v)
    have h := hcov (S u) (S v)
    rw [hTS,hTS] at h
    exact h
  rw [hB]
  exact hP.comp (hi.comp hS)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.dualPrecomposition_isInvertible_of_inverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isInvertible_of_bilinear_rotation_covariance
