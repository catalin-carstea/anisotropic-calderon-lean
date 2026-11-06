import Calderon.FiniteSmoothPhysicalSourceDecomposition
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic
attribute [local irreducible] harmonicSphereSubspace

theorem exists_exact_smooth_finite_fiveHalf_source_decomposition
    (n:ℕ) (u:R3→SphereSobolev (5/2:ℝ)) (hu:ContDiff ℝ ∞ u) (hc:HasCompactSupport u)
    (U:Fin n→Set R3) (hU:∀ i,IsOpen (U i)) (hCover:∀ y∈tsupport u,∃ i,y∈U i):
    ∃ w:Fin n→R3→SphereSobolev (5/2:ℝ),
      (∀ i,ContDiff ℝ ∞ (w i) ∧ HasCompactSupport (w i) ∧ tsupport (w i)⊆tsupport u∩U i) ∧
      (∀ y:R3,∑ i,w i y=u y) := by
  exact exists_exact_smooth_finite_source_decomposition n u hu hc U hU hCover

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
