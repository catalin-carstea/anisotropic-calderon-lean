import Calderon.SphereSobolevBalancedDualSmoothMiddle
import Calderon.CompactWithinJetBounds
import Calderon.ActualReferenceExtendedCenterInverseRoom
import Mathlib.Analysis.Calculus.TangentCone.Real
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily.DriftBootstrap
variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]
attribute [local irreducible] sphereSobolevInclusionL
lemma uniqueDiffOn_referencePhysicalTube
    (y0 : R3) (b d : ℝ) (hb : 0 < b) (hd : 0 < d) :
    UniqueDiffOn ℝ
      ((Icc (0 : ℝ) 1 ×ˢ (closedBall y0 b ×ˢ Icc (-d) d)) ×ˢ (univ : Set T)) := by
  classical
  let S : Set ((ℝ × (R3 × ℝ)) × T) :=
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 b ×ˢ Icc (-d) d)) ×ˢ univ
  let U : Set ((ℝ × (R3 × ℝ)) × T) :=
    (Ioo (0 : ℝ) 1 ×ˢ (ball y0 b ×ˢ Ioo (-d) d)) ×ˢ univ
  have hU : IsOpen U := (isOpen_Ioo.prod (isOpen_ball.prod isOpen_Ioo)).prod isOpen_univ
  have hUS : U ⊆ S := by
    intro z hz
    exact ⟨⟨⟨hz.1.1.1.le,hz.1.1.2.le⟩,ball_subset_closedBall hz.1.2.1,
      ⟨hz.1.2.2.1.le,hz.1.2.2.2.le⟩⟩,mem_univ _⟩
  have hBase : (((1/2 : ℝ),(y0,(0 : ℝ))),(0 : T)) ∈ U := by
    refine ⟨⟨⟨by norm_num,by norm_num⟩,mem_ball_self hb,?_⟩,mem_univ _⟩
    exact ⟨neg_lt_zero.mpr hd,hd⟩
  have hUnique : UniqueDiffOn ℝ S :=
    uniqueDiffOn_convex
      (((convex_Icc (0 : ℝ) 1).prod
        ((convex_closedBall y0 b).prod (convex_Icc (-d) d))).prod convex_univ)
      ⟨(((1/2 : ℝ),(y0,(0 : ℝ))),(0 : T)),interior_maximal hUS hU hBase⟩
  exact hUnique

lemma exists_nonneg_bound_iteratedFDerivWithin_on_physical_tube
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (y0 : R3) (b d : ℝ) (hb : 0 < b) (hd : 0 < d)
    (S : Set ((ℝ × (R3 × ℝ)) × T))
    (hS : S = (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 b ×ˢ Icc (-d) d)) ×ˢ univ)
    (G : ((ℝ × (R3 × ℝ)) × T) → F) (hG : ContDiffOn ℝ ∞ G S)
    (Kt : Set T) (hKt : IsCompact Kt) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 b ×ˢ Icc (-d) d)) ×ˢ Kt,
        ∀ n : ℕ, n ≤ N → ‖iteratedFDerivWithin ℝ n G S z‖ ≤ M := by
  have hUnique : UniqueDiffOn ℝ S := by
    rw [hS]
    exact uniqueDiffOn_referencePhysicalTube (T := T) y0 b d hb hd
  let C : Set ((ℝ × (R3 × ℝ)) × T) :=
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 b ×ˢ Icc (-d) d)) ×ˢ Kt
  have hC : IsCompact C :=
    (isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)).prod hKt
  have hCS : C ⊆ S := by
    rw [hS]
    exact fun z hz => ⟨hz.1,mem_univ _⟩
  exact exists_nonneg_bound_iteratedFDerivWithin_on_compact
    (X := ((ℝ × (R3 × ℝ)) × T)) (F := F) G S C hG hUnique hC hCS N

lemma exists_nonneg_bound_sphereSobolev_middle_jets_on_physical_tube
    (y0 : R3) (b d : ℝ) (hb : 0 < b) (hd : 0 < d)
    (S : Set ((ℝ × (R3 × ℝ)) × T))
    (hS : S = (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 b ×ˢ Icc (-d) d)) ×ˢ univ)
    (G : ((ℝ × (R3 × ℝ)) × T) → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (hG : ContDiffOn ℝ ∞ G S)
    (Kt : Set T) (hKt : IsCompact Kt) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 b ×ˢ Icc (-d) d)) ×ˢ Kt,
        ∀ n : ℕ, n ≤ N → ‖iteratedFDerivWithin ℝ n G S z‖ ≤ M := by
  exact exists_nonneg_bound_iteratedFDerivWithin_on_physical_tube
    (F := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    y0 b d hb hd S hS G hG Kt hKt N
end OAI.AnisotropicCalderon.SphereHarmonic
