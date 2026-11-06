import MixedKernelCompatibleGluing
import Mathlib.Topology.OpenPartialHomeomorph.Basic
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter
open scoped ContDiff Topology

/-- Every actual overlap component of same-level chart boxes reaches a common upper height. -/
theorem actual_chart_box_overlap_component_reaches_upper {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph (R3 × R3) (X × ℝ)) (B1 B2 : Set X)
    (a d1 d2 : ℝ) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hT1 : B1 ×ˢ Ioo (a-d1) (a+d1) ⊆ e.target)
    (hT2 : B2 ×ˢ Ioo (a-d2) (a+d2) ⊆ e.target) :
    let Ω := (e.source ∩ e ⁻¹' (B1 ×ˢ Ioo (a-d1) (a+d1))) ∩
      (e.source ∩ e ⁻¹' (B2 ×ˢ Ioo (a-d2) (a+d2)))
    ∀ z ∈ Ω, (connectedComponentIn Ω z ∩ {q | a < (e q).2}).Nonempty := by
  dsimp only
  intro z hz
  let Ω := (e.source ∩ e ⁻¹' (B1 ×ˢ Ioo (a-d1) (a+d1))) ∩
    (e.source ∩ e ⁻¹' (B2 ×ˢ Ioo (a-d2) (a+d2)))
  have hcoord : e z ∈ (B1 ×ˢ Ioo (a-d1) (a+d1)) ∩
      (B2 ×ˢ Ioo (a-d2) (a+d2)) := ⟨hz.1.2,hz.2.2⟩
  obtain ⟨h,hah,hseg⟩ := exists_vertical_segment_above_common_level B1 B2 a d1 d2 hd1 hd2
    (e z) hcoord
  let f : ℝ → R3 × R3 := fun t => e.symm ((e z).1,t)
  have hline : MapsTo (fun t : ℝ => ((e z).1,t)) (uIcc (e z).2 h) e.target :=
    fun t ht => hT1 (hseg t ht).1
  have hf : ContinuousOn f (uIcc (e z).2 h) :=
    e.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn hline
  have hstart : f (e z).2 = z := by
    change e.symm (e z) = z
    exact e.left_inv hz.1.1
  have hinside : MapsTo f (uIcc (e z).2 h) Ω := by
    intro t ht
    have htT := hline ht
    have heq : e (f t) = ((e z).1,t) := e.right_inv htT
    have hc := hseg t ht
    refine ⟨⟨e.map_target htT, ?_⟩,⟨e.map_target htT, ?_⟩⟩
    · change e (f t) ∈ B1 ×ˢ Ioo (a-d1) (a+d1)
      rw [heq]
      exact hc.1
    · change e (f t) ∈ B2 ×ˢ Ioo (a-d2) (a+d2)
      rw [heq]
      exact hc.2
  refine ⟨f h, continuous_interval_endpoint_mem_component (e z).2 h f hf hstart hinside, ?_⟩
  change a < (e (f h)).2
  rw [show e (f h) = ((e z).1,h) from e.right_inv (hline right_mem_uIcc)]
  exact hah

/-- Actual SAME-chart vertical geometry supplies compatibility on every overlap component. -/
theorem native_product_eq_on_actual_chart_box_overlap {X : Type*} [TopologicalSpace X]
    (S : KnownSideSourceData) (L lam : ℝ)
    (e : OpenPartialHomeomorph (R3 × R3) (X × ℝ)) (B1 B2 : Set X)
    (hB1 : IsOpen B1) (hB2 : IsOpen B2) (a d1 d2 : ℝ) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hT1 : B1 ×ˢ Ioo (a-d1) (a+d1) ⊆ e.target)
    (hT2 : B2 ×ˢ Ioo (a-d2) (a+d2) ⊆ e.target)
    (F G : R3 × R3 → ℝ) :
    let Ω := (e.source ∩ e ⁻¹' (B1 ×ˢ Ioo (a-d1) (a+d1))) ∩
      (e.source ∩ e ⁻¹' (B2 ×ˢ Ioo (a-d2) (a+d2)))
    ProductSolutionOn S L lam F Ω → ProductSolutionOn S L lam G Ω →
    (∀ z ∈ Ω, a < (e z).2 → F z = G z) → EqOn F G Ω := by
  dsimp only
  intro hF hG hseed
  let Ω := (e.source ∩ e ⁻¹' (B1 ×ˢ Ioo (a-d1) (a+d1))) ∩
    (e.source ∩ e ⁻¹' (B2 ×ˢ Ioo (a-d2) (a+d2)))
  let A := Ω ∩ (e.source ∩ e ⁻¹' ((univ : Set X) ×ˢ Ioi a))
  have hΩ : IsOpen Ω := (e.isOpen_inter_preimage (hB1.prod isOpen_Ioo)).inter
    (e.isOpen_inter_preimage (hB2.prod isOpen_Ioo))
  have hA : IsOpen A := hΩ.inter (e.isOpen_inter_preimage (isOpen_univ.prod isOpen_Ioi))
  apply native_product_eq_of_component_seed S L lam hΩ hA inter_subset_left hF hG
    (fun z hz => hseed z hz.1 hz.2.2.2)
  intro z hz
  obtain ⟨q,hqC,hqUpper⟩ := actual_chart_box_overlap_component_reaches_upper e B1 B2 a d1 d2
    hd1 hd2 hT1 hT2 z hz
  have hqΩ : q ∈ Ω := connectedComponentIn_subset Ω z hqC
  exact ⟨q,hqC,hqΩ,hqΩ.1.1, trivial,hqUpper⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
