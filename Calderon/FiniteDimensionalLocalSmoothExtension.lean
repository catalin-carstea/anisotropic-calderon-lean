import Calderon.LocalSmoothAmbientExtension

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily

theorem exists_contDiff_eq_near_compact_of_contDiffOn
    {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K S : Set X) (hK : IsCompact K) (hS : IsOpen S) (hKS : K ⊆ S)
    (u : X → V) (hu : ContDiffOn ℝ ∞ u S) :
    ∃ v : X → V, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧ ∀ x ∈ K, v =ᶠ[𝓝 x] u := by
  obtain ⟨W,hW,hKW,hWcompact⟩ := exists_isOpen_superset_and_isCompact_closure hK
  have hKSW : K ⊆ S ∩ W := fun x hx => ⟨hKS hx,hKW hx⟩
  obtain ⟨U,hU,hKU,hUclosure⟩ :=
    hK.exists_isOpen_closure_subset ((hS.inter hW).mem_nhdsSet.mpr hKSW)
  have hUcompact : IsCompact (closure U) :=
    hWcompact.of_isClosed_subset isClosed_closure
      (fun x hx => subset_closure (hUclosure hx).2)
  obtain ⟨V0,hV,hKV,hVclosure⟩ :=
    hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hKU)
  obtain ⟨χ,hχ,_,hSupport,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hU isClosed_closure hVclosure
  have hSmooth : ContDiff ℝ ∞ (fun x => χ x • u x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ S
    · exact hχ.contDiffAt.smul (hu.contDiffAt (hS.mem_nhds hx))
    · have hxOutside : x ∈ (closure U)ᶜ := fun hxU => hx (hUclosure hxU).1
      have hZero : (fun y => χ y • u y) =ᶠ[𝓝 x] (fun _ : X => (0 : V)) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxOutside] with y hy
        have hχZero : χ y = 0 := by
          apply notMem_support.mp
          rw [hSupport]
          exact fun hyU => hy (subset_closure hyU)
        simp only [hχZero,zero_smul]
      exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : X => (0 : V)) x).congr_of_eventuallyEq hZero
  have hχCompact : HasCompactSupport χ := by
    change IsCompact (closure (support χ))
    rw [hSupport]
    exact hUcompact
  refine ⟨fun x => χ x • u x,hSmooth,hχCompact.smul_right,?_⟩
  intro x hx
  filter_upwards [hV.mem_nhds (hKV hx)] with y hy
  have hχOne : χ y = 1 := (hOne y).mp (subset_closure hy)
  simp only [hχOne,one_smul]

end OAI.AnisotropicCalderon.DirichletFamily
