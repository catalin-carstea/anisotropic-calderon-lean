import Calderon.MixedRadialJetCalculus
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

/-! Nonradial jets decay quadratically; radial differentiation has its actual order. -/
set_option autoImplicit false
noncomputable section
open Set Function
open scoped ContDiff Topology BigOperators
namespace OAI.AnisotropicCalderon.ConnectionError

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def iteratedRadialDerivative : ℕ → (P × ℝ → V) → P × ℝ → V
  | 0,F => F
  | k+1,F => radialFirstDerivative (iteratedRadialDerivative k F)

theorem contDiff_iteratedRadialDerivative (k : ℕ) (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (iteratedRadialDerivative k F) := by
  induction k with
  | zero => exact hF
  | succ k ih => exact contDiff_radialFirstDerivative _ ih

/-- All radial prefixes commute with the genuine full nonradial parameter jets. -/
theorem iteratedRadialDerivative_parameterJetField (k j : ℕ) (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) :
    iteratedRadialDerivative k (parameterJetField j F) =
      parameterJetField j (iteratedRadialDerivative k F) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change radialFirstDerivative (iteratedRadialDerivative k (parameterJetField j F)) =
      parameterJetField j (radialFirstDerivative (iteratedRadialDerivative k F))
    rw [ih,radialFirstDerivative_parameterJetField j _ (contDiff_iteratedRadialDerivative k F hF)]

def CompactMixedRadialBounds (F : P × ℝ → V) (Q : Set P) (δ : ℝ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ N → ∀ p ∈ Q,
    ∀ r : ℝ, |r| ≤ δ →
      ‖parameterJetField j F (p,r)‖ ≤ C*r^2 ∧
      ‖parameterJetField j (iteratedRadialDerivative 1 F) (p,r)‖ ≤ C*|r| ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ N →
        ‖parameterJetField j (iteratedRadialDerivative k F) (p,r)‖ ≤ C

/-- Derive the corrected mixed bounds from actual zeroth and radial identities. -/
theorem compactMixedRadialBounds_of_zero_radial_jets (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) (s Q : Set P) (hs : IsOpen s) (hQ : IsCompact Q)
    (hQs : Q ⊆ closure s) (hzero : ∀ p ∈ s, F (p,0) = 0)
    (hjet : ∀ p ∈ s, HasDerivAt (fun r : ℝ => F (p,r)) 0 0)
    (δ : ℝ) (hδ : 0 ≤ δ) : CompactMixedRadialBounds F Q δ := by
  have hsingle (j k : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ p ∈ Q, ∀ r : ℝ, |r| ≤ δ →
      ‖parameterJetField j (iteratedRadialDerivative k F) (p,r)‖ ≤ D := by
    obtain ⟨D,hD⟩ := (hQ.prod (isCompact_Icc : IsCompact (Icc (-δ) δ))).exists_bound_of_continuousOn
      (contDiff_parameterJetField j _ (contDiff_iteratedRadialDerivative k F hF)).continuous.continuousOn
    exact ⟨max D 0,le_max_right _ _,fun p hp r hr =>
      (hD (p,r) ⟨hp,abs_le.mp hr⟩).trans (le_max_left _ _)⟩
  choose D hD hb using hsingle
  have hlinear (j : ℕ) (p : P) (hp : p ∈ Q) (r : ℝ) (hr : |r| ≤ δ) :
      ‖parameterJetField j (iteratedRadialDerivative 1 F) (p,r)‖ ≤ D j 2*|r| := by
    have hJ := contDiff_parameterJetField j F hF
    have hz := hasDerivAt_parameterJetField_zero_on_closure j F hF s hs hjet p (hQs hp)
    have hsecond (t : ℝ) (ht : |t| ≤ δ) :
        ‖deriv (deriv (fun u : ℝ => parameterJetField j F (p,u))) t‖ ≤ D j 2 := by
      rw [deriv_deriv_radialSlice _ hJ p t]
      change ‖iteratedRadialDerivative 2 (parameterJetField j F) (p,t)‖ ≤ D j 2
      rw [iteratedRadialDerivative_parameterJetField 2 j F hF]
      exact hb j 2 p hp t ht
    have h := norm_deriv_le_of_second_deriv_le (fun t : ℝ => parameterJetField j F (p,t))
      (hJ.comp (contDiff_const.prodMk contDiff_id)) δ (D j 2) hδ (hD j 2) hz hsecond r hr
    rw [deriv_radialSlice _ hJ p r,radialFirstDerivative_parameterJetField j F hF] at h
    exact h
  intro N
  obtain ⟨C0,hC0,hquad⟩ := exists_compact_uniform_parameterJet_quadratic_bound
    F hF s Q hs hQ hQs hzero hjet δ hδ N
  let S : ℝ := ∑ j ∈ Finset.range (N+1), ∑ k ∈ Finset.range (N+3), D j k
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hD j k))
  have hDj (j k : ℕ) (hj : j ≤ N) (hk : k ≤ N+2) : D j k ≤ S := by
    have hjm : j ∈ Finset.range (N+1) := Finset.mem_range.mpr (by omega)
    have hkm : k ∈ Finset.range (N+3) := Finset.mem_range.mpr (by omega)
    exact (Finset.single_le_sum (fun l _ => hD j l) hkm).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun k _ => hD l k)) hjm)
  refine ⟨C0+S,add_nonneg hC0 hS,?_⟩
  intro j hj p hp r hr
  refine ⟨(hquad j hj p hp r hr).trans
    (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg r)),
    (hlinear j p hp r hr).trans
      (mul_le_mul_of_nonneg_right (by have h := hDj j 2 hj (by omega); linarith) (abs_nonneg r)),?_⟩
  intro k hk hkN
  exact (hb j k p hp r hr).trans (by have h := hDj j k hj (by omega); linarith)

end OAI.AnisotropicCalderon.ConnectionError
