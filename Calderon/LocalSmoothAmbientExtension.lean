import Calderon.SmoothSobolevBridge
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Separation.Regular
/-! Localization: from a local smooth premise, via compact neighborhoods and
cutoffs. No global smooth premise is used. -/
set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem exists_smoothData_eq_near_compact
    (K S : Set R3) (hK : IsCompact K) (hS : IsOpen S) (hKS : K ⊆ S)
    (u : R3 → ℝ) (hu : ContDiffOn ℝ ∞ u S) :
    ∃ v : SmoothData, HasCompactSupport v.1 ∧ ∀ x ∈ K, v.1 =ᶠ[𝓝 x] u := by
  obtain ⟨W,hW,hKW,hWcompact⟩ := exists_isOpen_superset_and_isCompact_closure hK
  have hKSW : K ⊆ S ∩ W := fun x hx => ⟨hKS hx,hKW hx⟩
  obtain ⟨U,hU,hKU,hUclosure⟩ :=
    hK.exists_isOpen_closure_subset ((hS.inter hW).mem_nhdsSet.mpr hKSW)
  have hUcompact : IsCompact (closure U) :=
    hWcompact.of_isClosed_subset isClosed_closure
      (fun x hx => subset_closure (hUclosure hx).2)
  obtain ⟨V,hV,hKV,hVclosure⟩ :=
    hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hKU)
  obtain ⟨χ,hχ,_,hSupport,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hU isClosed_closure hVclosure
  have hSmooth : ContDiff ℝ ∞ (fun x => χ x * u x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ S
    · exact hχ.contDiffAt.mul (hu.contDiffAt (hS.mem_nhds hx))
    · have hxOutside : x ∈ (closure U)ᶜ := fun hxU => hx (hUclosure hxU).1
      have hZero : (fun y => χ y * u y) =ᶠ[𝓝 x] (fun _ : R3 => (0 : ℝ)) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxOutside] with y hy
        have hχZero : χ y = 0 := by
          apply notMem_support.mp
          rw [hSupport]
          exact fun hyU => hy (subset_closure hyU)
        simp only [hχZero,zero_mul]
      exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : R3 => (0 : ℝ)) x).congr_of_eventuallyEq hZero
  have hχCompact : HasCompactSupport χ := by
    change IsCompact (closure (support χ))
    rw [hSupport]
    exact hUcompact
  refine ⟨⟨fun x => χ x * u x,hSmooth⟩,hχCompact.mul_right,?_⟩
  intro x hx
  filter_upwards [hV.mem_nhds (hKV hx)] with y hy
  have hχOne : χ y = 1 := (hOne y).mp (subset_closure hy)
  simp only [hχOne,one_mul]

end OAI.AnisotropicCalderon.DirichletFamily
