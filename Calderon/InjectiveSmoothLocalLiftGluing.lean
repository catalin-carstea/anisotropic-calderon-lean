import Calderon.ActualPhysicalDensityOperatorGermCongruence
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore

theorem exists_smooth_compact_injective_lift_of_compatible_local_germs
    {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι:Type*}
    (I:E→L[ℝ]F) (hI:Function.Injective I) (K:Set R3) (hK:IsCompact K)
    (U:ι→Set R3) (hU:∀ i,IsOpen (U i)) (hCover:∀ y∈K,∃ i,y∈U i)
    (f:ι→R3→F)
    (hCompat:∀ i j,∀ y∈U i∩U j,f i y=f j y)
    (hZero:∀ i,∀ y∉K,f i y=0)
    (hLift:∀ i,∀ y∈U i,∃ w:R3→E,ContDiff ℝ ∞ w ∧
      (fun z => I (w z))=ᶠ[𝓝 y] f i):
    ∃ W:R3→E,ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧ tsupport W⊆K ∧
      ∀ i,∀ y∈U i,I (W y)=f i y := by
  classical
  let sel (y:R3) (hy:y∈K):ι := Classical.choose (hCover y hy)
  have hsel (y:R3) (hy:y∈K):y∈U (sel y hy) := Classical.choose_spec (hCover y hy)
  let G:R3→F := fun y => if hy:y∈K then f (sel y hy) y else 0
  have hGZero (y:R3) (hy:y∉K):G y=0 := by simp only [G,dite_eq_right hy]
  have hG (i:ι) (y:R3) (hy:y∈U i):G y=f i y := by
    by_cases hk:y∈K
    · rw [show G y=f (sel y hk) y from by simp only [G,dite_eq_left hk]]
      exact hCompat (sel y hk) i y ⟨hsel y hk,hy⟩
    · rw [show G y=0 from hGZero y hk,hZero i y hk]
  have hPoint:∀ y:R3,∃ v:E,I v=G y := by
    intro y
    by_cases hk:y∈K
    · obtain ⟨w,hw,hGraph⟩ := hLift (sel y hk) y (hsel y hk)
      exact ⟨w y,hGraph.self_of_nhds.trans (hG (sel y hk) y (hsel y hk)).symm⟩
    · exact ⟨0,(map_zero I).trans (hGZero y hk).symm⟩
  let W:R3→E := fun y => Classical.choose (hPoint y)
  have hWG:∀ y,I (W y)=G y := fun y => Classical.choose_spec (hPoint y)
  have hWZero (y:R3) (hy:y∉K):W y=0 := hI ((hWG y).trans ((hGZero y hy).trans (map_zero I).symm))
  have hSupp:tsupport W⊆K := by
    apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hk
    exact hy (hWZero y hk)
  have hSmooth:ContDiff ℝ ∞ W := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hk:y∈K
    · obtain ⟨i,hi⟩ := hCover y hk
      obtain ⟨w,hw,hGraph⟩ := hLift i y hi
      have hNear:W=ᶠ[𝓝 y]w := by
        filter_upwards [(hU i).mem_nhds hi,hGraph] with z hz hEq
        exact hI (((hWG z).trans (hG i z hz)).trans hEq.symm)
      exact hw.contDiffAt.congr_of_eventuallyEq hNear
    · have hNear:W=ᶠ[𝓝 y](fun _:R3 => (0:E)) := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hk] with z hz
        exact hWZero z hz
      exact contDiffAt_const.congr_of_eventuallyEq hNear
  exact ⟨W,hSmooth,hK.of_isClosed_subset (isClosed_tsupport W) hSupp,hSupp,fun i y hy => (hWG y).trans (hG i y hy)⟩

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
