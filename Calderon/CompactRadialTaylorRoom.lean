import Calderon.JointParameterTaylorRemainder

/-! Exact existential Taylor conclusion packaging. Full upfront:
general-boundary-multiplier-commutator-author-oct15-v001/
REPAIR-compact-Taylor-predicate-and-diagonal-v067.md. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
variable {Q P V : Type*}
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def HasCompactRadialTaylorRoom (F : Q × (P × ℝ) → V)
    (Ω : Set (Q × (P × ℝ))) (S : Set Q) (K : Set P) (ρ : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∃ M : ℝ, 0 ≤ M ∧
    (∀ p ∈ S ×ˢ (K ×ˢ Icc (-δ) δ), p ∈ Ω) ∧
    ∀ q ∈ S, ∀ y ∈ K, ∀ r : ℝ, |r| ≤ δ →
      F (q,(y,r)) = F (q,(y,0)) +
        r • radialFirstDerivative (fun p : P × ℝ => F (q,p)) (y,0) +
        r^2 • secondTaylorRemainder (fun t : ℝ => F (q,(y,t))) r ∧
      ‖secondTaylorRemainder (fun t : ℝ => F (q,(y,t))) r‖ ≤ M/2

theorem hasCompactRadialTaylorRoom_of_smooth_room
    (F : Q × (P × ℝ) → V) (Ω : Set (Q × (P × ℝ)))
    (S : Set Q) (K : Set P) (hS : IsCompact S) (hK : IsCompact K) (ρ : ℝ)
    (hRoom : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      (S ×ˢ (K ×ˢ Icc (-δ) δ) ⊆ Ω) ∧
      ∀ p ∈ S ×ˢ (K ×ˢ Icc (-δ) δ), ContDiffAt ℝ ∞ F p) :
    HasCompactRadialTaylorRoom F Ω S K ρ := by
  obtain ⟨δ,hδ,hδρ,hSubset,hSmooth⟩ := hRoom
  obtain ⟨M,hM,hTaylor⟩ := exists_compact_joint_uniform_secondTaylorRemainder
    F S K hS hK δ hδ.le hSmooth
  exact ⟨δ,hδ,hδρ,M,hM,hSubset,hTaylor⟩

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.HasCompactRadialTaylorRoom
#print axioms OAI.AnisotropicCalderon.ConnectionError.hasCompactRadialTaylorRoom_of_smooth_room
