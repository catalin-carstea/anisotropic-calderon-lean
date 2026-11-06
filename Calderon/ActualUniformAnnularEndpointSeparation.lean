import Calderon.ActualFixedSeparationInteriorGeometry
import Calderon.MixedKernelConstruction.MixedKernelPacketEndpointBounds
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConnectionError ConformalDepth

theorem exists_uniform_native_cover_annular_endpoint_separation
    (S:KnownSideSourceData) (L:ℝ) (cover:NativeNormalCover S L):
    ∃ r0 c B:ℝ,0 < r0 ∧ r0 ≤ cover.radiusCeiling ∧ 0 < c ∧ 0 < B ∧
      ∀ a b:ℝ,0 < a → b ≤ r0 → ∀ lambda∈Icc (0:ℝ) cover.dilationCeiling,
      ∀ i:Fin cover.count,∀ y∈cylinder∩(cover.packet i).centers,∀ r∈Icc a b,
      ∀ z∈sphere (0:R3) 1,(packetEndpoint S L (cover.packet i) lambda y r z,y)∈fixedSeparationSet B (c*a) := by
  classical
  choose rN cN CN hrN hrRhoN hrOneN hcN hCN HN using fun i:Fin cover.count =>
    exists_packet_endpoint_linear_bounds S L (cover.packet i)
  have hLower:∀ t:Finset (Fin cover.count),∃ r c:ℝ,0 < r ∧ 0 < c ∧
      ∀ i∈t,r ≤ rN i ∧ c ≤ cN i := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1,1,zero_lt_one,zero_lt_one,by simp⟩
    | @insert i t hi ih =>
      obtain ⟨r,c,hr,hc,H⟩ := ih
      refine ⟨min r (rN i),min c (cN i),lt_min hr (hrN i),lt_min hc (hcN i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with heq | hj
      · subst j;exact ⟨min_le_right _ _,min_le_right _ _⟩
      · exact ⟨(min_le_left _ _).trans (H j hj).1,(min_le_left _ _).trans (H j hj).2⟩
  obtain ⟨r,c,hr,hc,Hrc⟩ := hLower Finset.univ
  obtain ⟨CB,hCB⟩ := (Set.finite_range CN).bddAbove
  let r0:ℝ := min r (min 1 cover.radiusCeiling)
  let B:ℝ := max CB 1+3
  have hr0:0 < r0 := lt_min hr (lt_min zero_lt_one cover.radius_positive)
  have hr01:r0 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨r0,c,B,hr0,(min_le_right _ _).trans (min_le_right _ _),hc,by dsimp only [B];positivity,?_⟩
  intro a b ha hb lambda hlam i y hy s hs z hz
  have hs0:0 < s := ha.trans_le hs.1
  have hsN:s ≤ rN i := hs.2.trans (hb.trans ((min_le_left _ _).trans (Hrc i (Finset.mem_univ i)).1))
  have hs1:s ≤ 1 := hs.2.trans (hb.trans hr01)
  have hSphere:‖z‖=1 := by simpa only [mem_sphere_zero_iff_norm] using hz
  have hY:‖y‖ ≤ 2 := norm_le_two_of_mem_cylinder y hy.1
  have hyRoom:‖y-(cover.packet i).y0‖ ≤ 4*(cover.packet i).rho := ((cover.packet i).centers_room y hy.2).1.le
  obtain ⟨hLow,hHigh⟩ := HN i lambda ⟨hlam.1,hlam.2.trans cover.dilation_le_one⟩ y hyRoom s ⟨hs0.le,hsN⟩ z hSphere
  have hCNb:CN i ≤ max CB 1 := (hCB (Set.mem_range_self i)).trans (le_max_left _ _)
  have hDist:‖packetEndpoint S L (cover.packet i) lambda y s z-y‖ ≤ max CB 1 :=
    hHigh.trans ((mul_le_mul_of_nonneg_left hs1 (hCN i).le).trans (by simpa only [mul_one] using hCNb))
  have hX:=norm_add_le (packetEndpoint S L (cover.packet i) lambda y s z-y) y
  rw [sub_add_cancel] at hX
  exact ⟨by dsimp only [B];linarith only [hX,hDist,hY],by dsimp only [B];have hh:=le_max_right CB 1;linarith only [hY,hh],
    (mul_le_mul (Hrc i (Finset.mem_univ i)).2 hs.1 ha.le (hcN i).le).trans hLow⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
