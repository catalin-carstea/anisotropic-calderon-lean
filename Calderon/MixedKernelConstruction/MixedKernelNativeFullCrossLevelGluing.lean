import Calderon.MixedKernelConstruction.MixedKernelCompactLevelGluing
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology

/-- Restrict actual level gluing to its explicit union, retaining BOTH full original lower crosses. -/
theorem exists_native_full_cross_solution_from_common_level_boxes
    {X ι : Type*} [TopologicalSpace X]
    (S : KnownSideSourceData) (L lam : ℝ)
    (e : OpenPartialHomeomorph (R3 × R3) (X × ℝ))
    (B : ι → Set X) (hB : ∀ i, IsOpen (B i)) (a : ℝ) (d : ι → ℝ)
    (hd : ∀ i, 0<d i)
    (hT : ∀ i, B i ×ˢ Ioo (a-d i) (a+d i) ⊆ e.target)
    (A : Set (R3 × R3)) (hA : IsOpen A) (hARoom : A ⊆ dilatedOffDiagonal S lam)
    (hup : ∀ z ∈ A ∩ e.source, ∀ t : ℝ, (e z).2 ≤ t →
      ((e z).1,t) ∈ e.target → e.symm ((e z).1,t) ∈ A)
    (G : R3 × R3 → ℝ) (hG : ProductSolutionOn S L lam G A)
    (hG1 : ∀ z ∈ A, lam • z.2 ∈ S.W → G z=dilatedKernel1 S lam z)
    (hG2 : ∀ z ∈ A, lam • z.1 ∈ S.W → G z=dilatedKernel2 S lam z)
    (F : ι → R3 × R3 → ℝ)
    (hF : ∀ i, ProductSolutionOn S L lam (F i)
      (e.source ∩ e ⁻¹' (B i ×ˢ Ioo (a-d i) (a+d i))))
    (hFRoom : ∀ i, e.source ∩ e ⁻¹' (B i ×ˢ Ioo (a-d i) (a+d i)) ⊆ dilatedOffDiagonal S lam)
    (hF1 : ∀ i, ∀ z ∈ e.source ∩ e ⁻¹' (B i ×ˢ Ioo (a-d i) (a+d i)),
      lam • z.2 ∈ S.W → F i z=dilatedKernel1 S lam z)
    (hF2 : ∀ i, ∀ z ∈ e.source ∩ e ⁻¹' (B i ×ˢ Ioo (a-d i) (a+d i)),
      lam • z.1 ∈ S.W → F i z=dilatedKernel2 S lam z)
    (heq : ∀ i, ∀ z ∈ e.source ∩ e ⁻¹' (B i ×ˢ Ioo (a-d i) (a+d i)),
      a < (e z).2 → F i z=G z) :
    let M := A ∪ ⋃ i, e.source ∩ e ⁻¹' (B i ×ˢ Ioo (a-d i) (a+d i))
    IsOpen M ∧ M ⊆ dilatedOffDiagonal S lam ∧
      ∃ H : R3 × R3 → ℝ, ProductSolutionOn S L lam H M ∧ EqOn H G A ∧
        (∀ i, EqOn H (F i) (e.source ∩ e ⁻¹' (B i ×ˢ Ioo (a-d i) (a+d i)))) ∧
        (∀ z ∈ M, lam • z.2 ∈ S.W → H z=dilatedKernel1 S lam z) ∧
        (∀ z ∈ M, lam • z.1 ∈ S.W → H z=dilatedKernel2 S lam z) := by
  intro M
  let V : ι → Set (R3 × R3) := fun i =>
    e.source ∩ e ⁻¹' (B i ×ˢ Ioo (a-d i) (a+d i))
  obtain ⟨N,hN,hAN,hVN,H,hH,hHG,hHF⟩ :=
    exists_native_product_solution_from_common_level_boxes S L lam e B hB a d hd hT
      A hA hup G hG F hF heq
  have hMN : M ⊆ N := by
    intro z hz
    rcases hz with hA | hV
    · exact hAN hA
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hV
      exact hVN i hi
  have hM : IsOpen M := hA.union (isOpen_iUnion (fun i => e.isOpen_inter_preimage ((hB i).prod isOpen_Ioo)))
  refine ⟨hM,?_,H,productSolutionOn_mono hH hMN,hHG,hHF,?_,?_⟩
  · intro z hz
    rcases hz with hA | hV
    · exact hARoom hA
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hV
      exact hFRoom i hi
  · intro z hz hzW
    rcases hz with hzA | hzV
    · exact (hHG hzA).trans (hG1 z hzA hzW)
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hzV
      exact (hHF i hi).trans (hF1 i z hi hzW)
  · intro z hz hzW
    rcases hz with hzA | hzV
    · exact (hHG hzA).trans (hG2 z hzA hzW)
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hzV
      exact (hHF i hi).trans (hF2 i z hi hzW)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
