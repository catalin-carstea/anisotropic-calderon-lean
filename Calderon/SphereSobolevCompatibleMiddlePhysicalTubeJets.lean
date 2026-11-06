import Calderon.SphereSobolevBalancedDualSmoothMiddle
import Calderon.SphereSobolevPhysicalTubeJetBounds
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff
namespace OAI.AnisotropicCalderon.SphereHarmonic
variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]
attribute [local irreducible] sphereSobolevInclusionL
lemma exists_sphereSobolev_compatible_middle_jets_on_physical_tube
    (y0 : R3) (b d : ℝ) (hb : 0 < b) (hd : 0 < d)
    (S : Set ((ℝ × (R3 × ℝ)) × T))
    (hS : S = (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 b ×ˢ Icc (-d) d)) ×ˢ univ)
    (Gh : ((ℝ × (R3 × ℝ)) × T) → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ))
    (Gn : ((ℝ × (R3 × ℝ)) × T) → SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (hGh : ContDiffOn ℝ ∞ Gh S) (hGn : ContDiffOn ℝ ∞ Gn S)
    (hCompatible : ∀ z ∈ S, ∀ u : SphereSobolev (3/2 : ℝ),
      sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (Gh z u) =
        Gn z (sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u)) :
    ∃ G : ((ℝ × (R3 × ℝ)) × T) → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ),
      ContDiffOn ℝ ∞ G S ∧
      (∀ z ∈ S,
        (∀ u, G z (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) =
          sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (Gh z u)) ∧
        (∀ v, sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (G z v) =
          Gn z (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v)) ∧
        ‖G z‖ ≤ max ‖Gh z‖ ‖Gn z‖) ∧
      (∀ Kt : Set T, IsCompact Kt → ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧
        ∀ z ∈ (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 b ×ˢ Icc (-d) d)) ×ˢ Kt,
          ∀ n : ℕ, n ≤ N → ‖iteratedFDerivWithin ℝ n G S z‖ ≤ M) := by
  have hUnique : UniqueDiffOn ℝ S := by
    rw [hS]
    exact uniqueDiffOn_referencePhysicalTube (T := T) y0 b d hb hd
  exact (exists_contDiffOn_sphereSobolev_compatible_middle
    (X := ((ℝ × (R3 × ℝ)) × T)) S hUnique Gh Gn hGh hGn hCompatible).imp
      (fun G h => ⟨h.1,h.2,fun Kt hKt N =>
        exists_nonneg_bound_sphereSobolev_middle_jets_on_physical_tube
          y0 b d hb hd S hS G h.1 Kt hKt N⟩)
end OAI.AnisotropicCalderon.SphereHarmonic
