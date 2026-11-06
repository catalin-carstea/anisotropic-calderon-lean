import Calderon.MixedKernelConstruction.MixedKernelCompactLevelGluing
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology

/-- Every genuine zero-level chart point has a symmetric product box in any prescribed open output room. -/
theorem exists_actual_chart_zero_box
    {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph (R3 × R3) (X × ℝ))
    (q : R3 × R3) (hq : q ∈ e.source) (hzero : (e q).2=0)
    (V : Set (R3 × R3)) (hV : IsOpen V) (hqV : q ∈ V) :
    ∃ B : Set X, IsOpen B ∧ (e q).1 ∈ B ∧ ∃ d : ℝ, 0<d ∧
      B ×ˢ Ioo (-d) d ⊆ e.target ∧
      e.source ∩ e ⁻¹' (B ×ˢ Ioo (-d) d) ⊆ V := by
  let M : Set (X × ℝ) := e.target ∩ e.symm ⁻¹' V
  have hM : IsOpen M := e.symm.isOpen_inter_preimage hV
  have heq : ((e q).1,(0 : ℝ))=e q := by ext <;> simp [hzero]
  have hPoint : ((e q).1,(0 : ℝ)) ∈ M := by
    rw [heq]
    exact ⟨e.map_source hq,by change e.symm (e q) ∈ V;rw [e.left_inv hq];exact hqV⟩
  obtain ⟨B,J,hB,hJ,hbase,h0,hBJ⟩ := isOpen_prod_iff.mp hM (e q).1 0 hPoint
  obtain ⟨d,hd,hBall⟩ := Metric.isOpen_iff.mp hJ 0 h0
  have hInt : Ioo (-d) d ⊆ J := by
    intro t ht
    apply hBall
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    exact abs_lt.mpr ht
  have hBox : B ×ˢ Ioo (-d) d ⊆ M := fun a ha => hBJ ⟨ha.1,hInt ha.2⟩
  refine ⟨B,hB,hbase,d,hd,fun a ha => (hBox ha).1,?_⟩
  intro z hz
  have hh := (hBox hz.2).2
  change e.symm (e z) ∈ V at hh
  rw [e.left_inv hz.1] at hh
  exact hh

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
