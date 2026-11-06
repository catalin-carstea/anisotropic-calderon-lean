import Calderon.LocalUniformTaylorRemainder

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
variable {Q P V : Type*}
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem exists_compact_joint_uniform_secondTaylorRemainder
    (F : Q × (P × ℝ) → V) (S : Set Q) (K : Set P)
    (hS : IsCompact S) (hK : IsCompact K) (δ : ℝ) (hδ : 0 ≤ δ)
    (hF : ∀ p ∈ S ×ˢ (K ×ˢ Icc (-δ) δ), ContDiffAt ℝ ∞ F p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ S, ∀ y ∈ K, ∀ r : ℝ, |r| ≤ δ →
      F (q,(y,r)) = F (q,(y,0)) +
        r • radialFirstDerivative (fun p : P × ℝ => F (q,p)) (y,0) +
        r^2 • secondTaylorRemainder (fun t : ℝ => F (q,(y,t))) r ∧
      ‖secondTaylorRemainder (fun t : ℝ => F (q,(y,t))) r‖ ≤ C/2 := by
  let G : (Q × P) × ℝ → V := fun p => F (p.1.1,(p.1.2,p.2))
  have hG (p : (Q × P) × ℝ) (hp : p ∈ (S ×ˢ K) ×ˢ Icc (-δ) δ) :
      ContDiffAt ℝ ∞ G p :=
    (hF (p.1.1,(p.1.2,p.2)) ⟨hp.1.1,hp.1.2,hp.2⟩).comp p
      (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))
  obtain ⟨C,hC,hTaylor⟩ := exists_compact_local_uniform_secondTaylorRemainder
    G (S ×ˢ K) (hS.prod hK) δ hδ hG
  refine ⟨C,hC,?_⟩
  intro q hq y hy r hr
  have hz : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith,hδ⟩
  have hG0 := hG ((q,y),0) ⟨⟨hq,hy⟩,hz⟩
  have hSlice : ContDiffAt ℝ ∞ (fun p : P × ℝ => F (q,p)) (y,0) :=
    (hF (q,(y,0)) ⟨hq,hy,hz⟩).comp (y,0)
      (contDiffAt_const.prodMk contDiffAt_id)
  have hd : radialFirstDerivative G ((q,y),0) =
      radialFirstDerivative (fun p : P × ℝ => F (q,p)) (y,0) := by
    rw [← deriv_radialSlice_of_differentiableAt G (q,y) 0
      (hG0.differentiableAt (by simp))]
    rw [← deriv_radialSlice_of_differentiableAt (fun p : P × ℝ => F (q,p)) y 0
      (hSlice.differentiableAt (by simp))]
  have ht := hTaylor (q,y) ⟨hq,hy⟩ r hr
  rw [hd] at ht
  exact ht

end OAI.AnisotropicCalderon.ConnectionError
