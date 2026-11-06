import Calderon.MixedRadialDerivativeBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! UNCOMPILED author proposal. EXPANSION.md D6 was saved before source.
Only nonradial jets decay linearly; radial prefixes are uniformly bounded. -/
set_option autoImplicit false
noncomputable section
open Set Function
open scoped ContDiff Topology BigOperators
namespace OAI.AnisotropicCalderon.ConnectionError
variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def CompactMixedLinearBounds (F : U × ℝ → V) (Q : Set U) (δ : ℝ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ N → ∀ p ∈ Q,
    ∀ r : ℝ, |r| ≤ δ →
      ‖parameterJetField j F (p,r)‖ ≤ C*|r| ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ N →
        ‖parameterJetField j (iteratedRadialDerivative k F) (p,r)‖ ≤ C

theorem compactMixedLinearBounds_of_zero_slice
    (F : U × ℝ → V) (hF : ContDiff ℝ ∞ F) (Q : Set U) (hQ : IsCompact Q)
    (hzero : ∀ p : U, F (p,0) = 0) (δ : ℝ) (hδ : 0 ≤ δ) :
    CompactMixedLinearBounds F Q δ := by
  have hsingle (j k : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ p ∈ Q, ∀ r : ℝ, |r| ≤ δ →
      ‖parameterJetField j (iteratedRadialDerivative k F) (p,r)‖ ≤ D := by
    obtain ⟨D,hD⟩ := (hQ.prod (isCompact_Icc : IsCompact (Icc (-δ) δ))).exists_bound_of_continuousOn
      (contDiff_parameterJetField j _ (contDiff_iteratedRadialDerivative k F hF)).continuous.continuousOn
    exact ⟨max D 0,le_max_right _ _,fun p hp r hr =>
      (hD (p,r) ⟨hp,abs_le.mp hr⟩).trans (le_max_left _ _)⟩
  choose D hD hb using hsingle
  have hlinear (j : ℕ) (p : U) (hp : p ∈ Q) (r : ℝ) (hr : |r| ≤ δ) :
      ‖parameterJetField j F (p,r)‖ ≤ D j 1*|r| := by
    have hJ := contDiff_parameterJetField j F hF
    have hz : parameterJetField j F (p,0) = 0 :=
      parameterJetField_zero_on_closure j F hF univ isOpen_univ
        (fun x _ => hzero x) p (by simp)
    have hs : ContDiff ℝ ∞ (fun t : ℝ => parameterJetField j F (p,t)) :=
      hJ.comp (contDiff_const.prodMk contDiff_id)
    have hd (t : ℝ) (ht : t ∈ Icc (-δ) δ) :
        ‖deriv (fun u : ℝ => parameterJetField j F (p,u)) t‖ ≤ D j 1 := by
      rw [deriv_radialSlice _ hJ p t,radialFirstDerivative_parameterJetField j F hF]
      exact hb j 1 p hp t (abs_le.mpr ht)
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t (_ : t ∈ Icc (-δ) δ) => hs.differentiable (by simp) t)
      hd (convex_Icc (-δ) δ) (show (0 : ℝ) ∈ Icc (-δ) δ from ⟨by linarith,hδ⟩)
      (abs_le.mp hr)
    simpa only [hz,sub_zero,Real.norm_eq_abs] using h
  intro N
  let S : ℝ := ∑ j ∈ Finset.range (N+1), ∑ k ∈ Finset.range (N+2), D j k
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hD j k))
  have hDj (j k : ℕ) (hj : j ≤ N) (hk : k ≤ N+1) : D j k ≤ S := by
    have hjm : j ∈ Finset.range (N+1) := Finset.mem_range.mpr (by omega)
    have hkm : k ∈ Finset.range (N+2) := Finset.mem_range.mpr (by omega)
    exact (Finset.single_le_sum (fun l _ => hD j l) hkm).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun k _ => hD l k)) hjm)
  refine ⟨S,hS,?_⟩
  intro j hj p hp r hr
  refine ⟨(hlinear j p hp r hr).trans
    (mul_le_mul_of_nonneg_right (hDj j 1 hj (by omega)) (abs_nonneg r)),?_⟩
  intro k hk hkN
  exact (hb j k p hp r hr).trans (hDj j k hj (by omega))

end OAI.AnisotropicCalderon.ConnectionError
