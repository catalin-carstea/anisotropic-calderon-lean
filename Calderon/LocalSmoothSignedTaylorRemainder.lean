import Calderon.SmoothSignedTaylorRemainder

/-! Upfront: general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION-local-signed-remainder-compact-tube-v037.md. Genuine compact
local extension and uniform tube transfer for the actual signed integral. -/
set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
open DirichletFamily
variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

lemma contDiffAt_secondTaylorRemainder_joint_of_open_segment
    (F : P × ℝ → V) (Ω : Set (P × ℝ)) (hΩ : IsOpen Ω)
    (hF : ContDiffOn ℝ ∞ F Ω) (p : P) (r : ℝ)
    (hSegment : ∀ a ∈ Icc (0 : ℝ) 1, (p,a*r) ∈ Ω) :
    ContDiffAt ℝ ∞ (fun z : P × ℝ => secondTaylorRemainder (fun t : ℝ => F (z.1,t)) z.2) (p,r) := by
  let K : Set (P × ℝ) := (fun a : ℝ => (p,a*r)) '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image (continuous_const.prodMk (continuous_id.mul_const r))
  have hKΩ : K ⊆ Ω := by
    rintro _ ⟨a,ha,rfl⟩
    exact hSegment a ha
  obtain ⟨g,hg,_,hEq⟩ := exists_contDiff_eq_near_compact_of_contDiffOn K Ω hK hΩ hKΩ F hF
  let U : Set (P × ℝ) := interior {x | g x = F x}
  have hU : IsOpen U := isOpen_interior
  have hKU : K ⊆ U := by
    intro x hx
    exact mem_interior_iff_mem_nhds.mpr (hEq x hx)
  have hULocal (x : P × ℝ) (hx : x ∈ U) : g =ᶠ[𝓝 x] F := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (interior_subset : interior {z : P × ℝ | g z = F z} ⊆
      {z : P × ℝ | g z = F z}) hy
  have hTubeOpen : IsOpen {w : (P × ℝ) × ℝ | (w.1.1,w.2*w.1.2) ∈ U} :=
    hU.preimage (continuous_fst.fst.prodMk (continuous_snd.mul continuous_fst.snd))
  have hTube : ∀ᶠ z in 𝓝 (p,r), ∀ a ∈ Icc (0 : ℝ) 1, (z.1,a*z.2) ∈ U := by
    apply (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).eventually_forall_of_forall_eventually
    intro a ha
    exact hTubeOpen.mem_nhds (hKU ⟨a,ha,rfl⟩)
  have hRemainder : (fun z : P × ℝ => secondTaylorRemainder (fun t : ℝ => g (z.1,t)) z.2)
      =ᶠ[𝓝 (p,r)] (fun z : P × ℝ => secondTaylorRemainder (fun t : ℝ => F (z.1,t)) z.2) := by
    filter_upwards [hTube] with z hz
    apply secondTaylorRemainder_eq_of_locallyEq_on_segment
    intro a ha
    exact (continuousAt_const.prodMk continuousAt_id).eventually (hULocal _ (hz a ha))
  exact (contDiff_secondTaylorRemainder_joint g hg).contDiffAt.congr_of_eventuallyEq hRemainder.symm

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiffAt_secondTaylorRemainder_joint_of_open_segment
