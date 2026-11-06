import Calderon.ActualMixedKernelGlobalSurfaceExtension

set_option autoImplicit false
noncomputable section
open Set Metric Filter Function
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

theorem exists_contDiff_compact_extension_eq_near_compact
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A U : Set R3) (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U)
    (psi : R3 → F) (hpsi : ContDiffOn ℝ ∞ psi U) :
    ∃ psiGlobal : R3 → F, ContDiff ℝ ∞ psiGlobal ∧ HasCompactSupport psiGlobal ∧
      ∀ y ∈ A, psiGlobal =ᶠ[𝓝 y] psi := by
  obtain ⟨W,hW,hAW,hWcompact⟩ := exists_isOpen_superset_and_isCompact_closure hA
  have hAUW : A ⊆ U ∩ W := fun x hx => ⟨hAU hx,hAW hx⟩
  obtain ⟨B,hB,hAB,hBclosure⟩ :=
    hA.exists_isOpen_closure_subset ((hU.inter hW).mem_nhdsSet.mpr hAUW)
  have hBcompact : IsCompact (closure B) :=
    hWcompact.of_isClosed_subset isClosed_closure
      (fun x hx => subset_closure (hBclosure hx).2)
  obtain ⟨C,hC,hAC,hCclosure⟩ :=
    hA.exists_isOpen_closure_subset (hB.mem_nhdsSet.mpr hAB)
  obtain ⟨chi,hchi,_,hSupport,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hB isClosed_closure hCclosure
  have hSmooth : ContDiff ℝ ∞ (fun x => chi x • psi x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact hchi.contDiffAt.smul (hpsi.contDiffAt (hU.mem_nhds hx))
    · have hxOutside : x ∈ (closure B)ᶜ := fun hxB => hx (hBclosure hxB).1
      have hZero : (fun y => chi y • psi y) =ᶠ[𝓝 x] (fun _ : R3 => (0 : F)) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxOutside] with y hy
        have hchiZero : chi y = 0 := by
          apply notMem_support.mp
          rw [hSupport]
          exact fun hyB => hy (subset_closure hyB)
        simp only [hchiZero,zero_smul]
      exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : R3 => (0 : F)) x).congr_of_eventuallyEq hZero
  have hSub : Function.support (fun y => chi y • psi y) ⊆ B := by
    intro x hx
    by_contra hn
    have hZero : chi x = 0 := by
      apply notMem_support.mp
      rwa [hSupport]
    exact hx (by simp only [hZero,zero_smul])
  have hCompact : HasCompactSupport (fun x => chi x • psi x) :=
    hBcompact.of_isClosed_subset isClosed_closure (closure_mono hSub)
  refine ⟨fun x => chi x • psi x,hSmooth,hCompact,?_⟩
  intro x hx
  filter_upwards [hC.mem_nhds (hAC hx)] with y hy
  have hchiOne : chi y = 1 := (hOne y).mp (subset_closure hy)
  simp only [hchiOne,one_smul]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
