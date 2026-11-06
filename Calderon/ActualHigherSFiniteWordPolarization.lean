import Calderon.ActualHigherSDoubleQuarticIdentity

/-! Finite real weighted polarization, retaining all ordered coefficient pairs.
The real inner-product symmetry is explicit before scalar normalization. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSFiniteWordPolarization

lemma norm_weighted_word_sum_sq {V Q κ : Type*} [Fintype κ]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    (K : V →L[ℝ] Q) (c : κ → ℝ) (f : κ → V) :
    ‖K (∑ z : κ, c z • f z)‖^2 =
      ∑ z : κ, ∑ v : κ, (c z*c v)*⟪K (f z), K (f v)⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
    inner_smul_right, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro v _
  simp only [real_inner_comm (K (f v)) (K (f z))] <;> ring

lemma norm_weighted_word_sum_sq_sub {V Q κ : Type*} [Fintype κ]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    (K : V →L[ℝ] Q) (c : κ → ℝ) (f r : κ → V) (R : κ → κ → ℝ)
    (hR : ∀ z v, ⟪K (f z), K (f v)⟫_ℝ - ⟪K (r z), K (r v)⟫_ℝ = R z v) :
    ‖K (∑ z : κ, c z • f z)‖^2 - ‖K (∑ z : κ, c z • r z)‖^2 =
      ∑ z : κ, ∑ v : κ, (c z*c v)*R z v := by
  rw [norm_weighted_word_sum_sq K c f, norm_weighted_word_sum_sq K c r,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [← mul_sub, hR z v]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSFiniteWordPolarization
