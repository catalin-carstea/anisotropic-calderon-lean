import MixedKernelCompatibleGluing
import MixedKernelObservedOutputRooms
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter
open scoped ContDiff Topology

/-- Actual upward paths and existing UCP identify the new solution on the old positive side. -/
theorem eqOn_positive_chart_box_of_monotone
    {K : Type*} [NormedAddCommGroup K] (S : KnownSideSourceData) (L lam : ℝ)
    (e : OpenPartialHomeomorph R3 (ℝ × K)) (l ε R : ℝ)
    (hε : 0 < ε) (hl : 4 * ε < l) (hR : 0 < R)
    (hDt : PhaseCoordinates.closedD l ε R ⊆ e.target)
    (O1 O2 S2 : Set R3) (hO1 : IsOpen O1) (hO2 : IsOpen O2) (hS2 : IsOpen S2)
    (hO2def : O2 = e.symm '' PhaseCoordinates.roomO l ε R)
    (hS2def : S2 = e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))
    (U : Set (R3 × R3)) (hU : IsOpen U) (rho : R3 × R3 → ℝ)
    (hrho : ContinuousOn rho U) (hboxU : O1 ×ˢ O2 ⊆ U)
    (hknown : O1 ×ˢ S2 ⊆ {z | z ∈ U ∧ 0 < rho z})
    (hmono : ∀ x ∈ O1, ∀ q ∈ Metric.ball (0 : K) (R/2),
      MonotoneOn (fun s : ℝ => rho (x,e.symm (s,q))) (Ioo (-ε) (l+3*ε/2)))
    (F G : R3 × R3 → ℝ)
    (hF : ProductSolutionOn S L lam F {z | z ∈ U ∧ 0 < rho z})
    (hG : ProductSolutionOn S L lam G (O1 ×ˢ O2))
    (hfirst : EqOn G F (O1 ×ˢ S2)) :
    EqOn G F ((O1 ×ˢ O2) ∩ {z | z ∈ U ∧ 0 < rho z}) := by
  let B := O1 ×ˢ O2
  let N := B ∩ {z : R3 × R3 | z ∈ U ∧ 0 < rho z}
  let A := O1 ×ˢ (S2 ∩ O2)
  have hOld : IsOpen {z : R3 × R3 | z ∈ U ∧ 0 < rho z} :=
    hrho.isOpen_inter_preimage hU isOpen_Ioi
  have hN : IsOpen N := (hO1.prod hO2).inter hOld
  have hA : IsOpen A := hO1.prod (hS2.inter hO2)
  have hAN : A ⊆ N := fun z hz => ⟨⟨hz.1,hz.2.2⟩,hknown ⟨hz.1,hz.2.1⟩⟩
  have hOT : (PhaseCoordinates.roomO l ε R : Set (ℝ × K)) ⊆ e.target :=
    PhaseCoordinates.roomO_subset_closedO.trans
      ((PhaseCoordinates.closedO_subset_roomD hε hl hR).trans
        (PhaseCoordinates.roomD_subset_closedD.trans hDt))
  apply native_product_eq_of_interval_seed S L lam hN hA hAN
    (productSolutionOn_mono hG inter_subset_left) (productSolutionOn_mono hF inter_subset_right)
    (fun z hz => hfirst ⟨hz.1,hz.2.1⟩)
  intro z hz
  rcases z with ⟨x,y⟩
  have hx : x ∈ O1 := hz.1.1
  have hy : y ∈ e.symm '' PhaseCoordinates.roomO l ε R := hO2def ▸ hz.1.2
  rcases hy with ⟨q,hq,rfl⟩
  have hqH : -ε < q.1 ∧ q.1 < l+3*ε/2 := hq.1
  have hqB : q.2 ∈ Metric.ball (0 : K) (R/2) := hq.2
  have hqStopRadius : q.2 ∈ Metric.ball (0 : K) (7*R/8) :=
    (Metric.ball_subset_ball (by linarith : R/2 ≤ 7*R/8)) hqB
  by_cases hqtop : q.1 ≤ l+ε
  · have hseg (t : ℝ) (ht : t ∈ uIcc q.1 (l+ε)) :
        ((t,q.2) : ℝ × K) ∈ PhaseCoordinates.roomO l ε R := by
      have ht' : q.1 ≤ t ∧ t ≤ l+ε := by simpa only [uIcc_of_le hqtop,mem_Icc] using ht
      exact ⟨⟨hqH.1.trans_le ht'.1,by linarith [ht'.2]⟩,hqB⟩
    have hline : MapsTo (fun t : ℝ => (t,q.2)) (uIcc q.1 (l+ε)) e.target :=
      fun t ht => hOT (hseg t ht)
    let f : ℝ → R3 × R3 := fun t => (x,e.symm (t,q.2))
    have hf : ContinuousOn f (uIcc q.1 (l+ε)) :=
      continuousOn_const.prodMk (e.continuousOn_symm.comp
        (continuous_id.prodMk continuous_const).continuousOn hline)
    have hin : MapsTo f (uIcc q.1 (l+ε)) N := by
      intro t ht
      have ht' : q.1 ≤ t ∧ t ≤ l+ε := by simpa only [uIcc_of_le hqtop,mem_Icc] using ht
      have hb : f t ∈ B := ⟨hx,hO2def.symm ▸ mem_image_of_mem e.symm (hseg t ht)⟩
      have hp : 0 < rho (f t) := hz.2.2.trans_le
        (hmono x hx q.2 hqB hqH (hseg t ht).1 ht'.1)
      exact ⟨hb,hboxU hb,hp⟩
    have htopS : ((l+ε,q.2) : ℝ × K) ∈
        PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R :=
      Or.inl ⟨⟨by linarith,by linarith⟩,hqStopRadius⟩
    have hEnd : f (l+ε) ∈ A :=
      ⟨hx,hS2def.symm ▸ mem_image_of_mem e.symm htopS,
        hO2def.symm ▸ mem_image_of_mem e.symm (hseg (l+ε) right_mem_uIcc)⟩
    exact ⟨q.1,l+ε,f,hf,rfl,hin,hEnd⟩
  · have hqStop : q ∈ PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R :=
      Or.inl ⟨⟨by linarith,by linarith⟩,hqStopRadius⟩
    have hqS : e.symm q ∈ S2 := hS2def.symm ▸ mem_image_of_mem e.symm hqStop
    exact ⟨0,0,fun _ => (x,e.symm q),continuousOn_const,rfl,
      (fun _ _ => hz),hx,hqS,hz.1.2⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
