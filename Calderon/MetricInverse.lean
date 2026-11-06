import Calderon.ConnectionField
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def inverseMetricField (M : E → E →L[ℝ] E) : E → E →L[ℝ] E :=
  fun x => Ring.inverse (M x)

theorem isUnit_of_strictly_positive [FiniteDimensional ℝ E] (M : E →L[ℝ] E)
    (hM : ∀ X : E, X ≠ 0 → 0 < inner ℝ (M X) X) : IsUnit M := by
  have hi : Function.Injective M := by
    intro X Y hXY
    by_contra hne
    have hp := hM (X-Y) (sub_ne_zero.mpr hne)
    have hz : M (X-Y) = 0 := by rw [map_sub,hXY,sub_self]
    simp only [hz,inner_zero_left,lt_self_iff_false] at hp
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  exact ⟨hi,(LinearMap.injective_iff_surjective (f := M.toLinearMap)).mp hi⟩

theorem contDiff_inverseMetricField (M : E → E →L[ℝ] E)
    (hM : ContDiff ℝ ∞ M) (hunit : ∀ x, IsUnit (M x)) :
    ContDiff ℝ ∞ (inverseMetricField M) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨u,hu⟩ := hunit x
  have hinv : ContDiffAt ℝ ∞ Ring.inverse (M x) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact hinv.comp x hM.contDiffAt

theorem inverseMetricField_apply_metric (M : E → E →L[ℝ] E)
    (hunit : ∀ x, IsUnit (M x)) (x X : E) : inverseMetricField M x (M x X) = X := by
  have h := Ring.inverse_mul_cancel (M x) (hunit x)
  exact congrArg (fun A : E →L[ℝ] E => A X) h

theorem metric_apply_inverseMetricField (M : E → E →L[ℝ] E)
    (hunit : ∀ x, IsUnit (M x)) (x X : E) : M x (inverseMetricField M x X) = X := by
  have h := Ring.mul_inverse_cancel (M x) (hunit x)
  exact congrArg (fun A : E →L[ℝ] E => A X) h

theorem contDiff_actualMetricConnection [FiniteDimensional ℝ E]
    (M : E → E →L[ℝ] E) (hM : ContDiff ℝ ∞ M)
    (hpos : ∀ x X, X ≠ 0 → 0 < inner ℝ (M x X) X) :
    ContDiff ℝ ∞ (coordinateConnectionField (inverseMetricField M) M) :=
  contDiff_coordinateConnectionField_infty _ _
    (contDiff_inverseMetricField M hM (fun x => isUnit_of_strictly_positive (M x) (hpos x))) hM

#print axioms isUnit_of_strictly_positive
#print axioms contDiff_inverseMetricField
#print axioms contDiff_actualMetricConnection
end OAI.AnisotropicCalderon.ConnectionError
