import Calderon.LocalRadialDerivative
import Calderon.SignedOperatorTaylorRemainder

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem exists_compact_local_uniform_secondTaylorRemainder
    (F : P × ℝ → V) (K : Set P) (hK : IsCompact K) (δ : ℝ) (hδ : 0 ≤ δ)
    (hF : ∀ p ∈ K ×ˢ Icc (-δ) δ, ContDiffAt ℝ ∞ F p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ r : ℝ, |r| ≤ δ →
      F (y,r) = F (y,0) + r • radialFirstDerivative F (y,0) +
        r^2 • secondTaylorRemainder (fun t : ℝ => F (y,t)) r ∧
      ‖secondTaylorRemainder (fun t : ℝ => F (y,t)) r‖ ≤ C/2 := by
  have hDDc : ContinuousOn (radialSecondDerivative F) (K ×ˢ Icc (-δ) δ) :=
    fun p hp => (contDiffAt_radialSecondDerivative F p (hF p hp)).continuousAt.continuousWithinAt
  obtain ⟨M,hM⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hDDc
  let C : ℝ := max M 0
  refine ⟨C,le_max_right _ _,?_⟩
  intro y hy r hr
  have hRoom (t : ℝ) (ht : |t| ≤ δ) : (y,t) ∈ K ×ˢ Icc (-δ) δ :=
    ⟨hy,abs_le.mp ht⟩
  have hSlice (t : ℝ) (ht : |t| ≤ δ) :
      ContDiffAt ℝ ∞ (fun s : ℝ => F (y,s)) t :=
    (hF (y,t) (hRoom t ht)).comp t (contDiffAt_const.prodMk contDiffAt_id)
  have hSegment (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) r) : |t| ≤ δ :=
    (show |t| ≤ |r| from by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc ht).trans hr
  constructor
  · have hTaylor := signed_taylor_integral_remainder (fun t : ℝ => F (y,t)) r
      (fun t ht => hSlice t (hSegment t ht))
    rw [deriv_radialSlice_of_differentiableAt F y 0
      ((hF (y,0) (hRoom 0 (by simpa using hδ))).differentiableAt (by simp))] at hTaylor
    exact hTaylor
  · apply norm_secondTaylorRemainder_le _ r C (le_max_right _ _)
    intro t ht
    have htr : |t*r| ≤ δ := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg r)).trans (by simpa using hr)
    rw [deriv_deriv_radialSlice_of_contDiffAt F y (t*r) (hF (y,t*r) (hRoom (t*r) htr))]
    exact (hM (y,t*r) (hRoom (t*r) htr)).trans (le_max_left _ _)

end OAI.AnisotropicCalderon.ConnectionError
