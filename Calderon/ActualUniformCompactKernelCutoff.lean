import Calderon.ActualMixedKernelConstruction
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Bounds
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

theorem contDiff_product_cutoff_mul (U:Set (R3×R3)) (hU:IsOpen U)
    (chi:R3×R3→ℝ) (hchi:ContDiff ℝ ∞ chi) (hchiU:tsupport chi⊆U)
    (F:R3×R3→ℝ) (hF:ContDiffOn ℝ ∞ F U):ContDiff ℝ ∞ (fun z => chi z*F z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz:z∈U
  · exact hchi.contDiffAt.mul (hF.contDiffAt (hU.mem_nhds hz))
  · have hzOut:z∉tsupport chi := fun hh => hz (hchiU hh)
    have hzero:(fun w => chi w*F w)=ᶠ[𝓝 z] (fun _:R3×R3 => (0:ℝ)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzOut] with w hw
      simp only [hw,Pi.zero_apply,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

theorem exists_compact_product_plateau_cutoff
    (K U:Set (R3×R3)) (hK:IsCompact K) (hU:IsOpen U) (hKU:K⊆U):
    ∃ chi:R3×R3→ℝ,ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧ tsupport chi⊆U ∧
      ∀ z∈K,chi=ᶠ[𝓝 z] (fun _:R3×R3 => (1:ℝ)) := by
  obtain ⟨W,hW,hKW,hWcompact⟩ := exists_isOpen_superset_and_isCompact_closure hK
  have hKUW:K⊆U∩W := fun z hz => ⟨hKU hz,hKW hz⟩
  obtain ⟨A,hA,hKA,hAclosure⟩ := hK.exists_isOpen_closure_subset ((hU.inter hW).mem_nhdsSet.mpr hKUW)
  have hAcompact:IsCompact (closure A) := hWcompact.of_isClosed_subset isClosed_closure
    (fun z hz => subset_closure (hAclosure hz).2)
  obtain ⟨B,hB,hKB,hBclosure⟩ := hK.exists_isOpen_closure_subset (hA.mem_nhdsSet.mpr hKA)
  obtain ⟨chi,hchi,_,hSupport,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n:=(⊤:ℕ∞)) hA isClosed_closure hBclosure
  have ht:tsupport chi=closure A := by unfold tsupport;rw [hSupport]
  refine ⟨chi,hchi,by change IsCompact (tsupport chi);rw [ht];exact hAcompact,?_,?_⟩
  · rw [ht]
    exact fun z hz => (hAclosure hz).1
  · intro z hz
    filter_upwards [hB.mem_nhds (hKB hz)] with w hw
    exact (hOne w).mp (subset_closure hw)

theorem exists_uniform_product_cutoff_joint_jet_bound
    (U:Set (R3×R3)) (hU:IsOpen U) (chi:R3×R3→ℝ) (hchi:ContDiff ℝ ∞ chi)
    (hchic:HasCompactSupport chi) (hchiU:tsupport chi⊆U):
    ∃ C:ℕ→ℝ,(∀ n,0 < C n) ∧ ∀ (F:R3×R3→ℝ),ContDiffOn ℝ ∞ F U →
      ∀ n:ℕ,∀ M:ℝ,0 ≤ M → (∀ j ≤ n,∀ z∈U,‖iteratedFDeriv ℝ j F z‖ ≤ M) →
      ∀ z:R3×R3,‖iteratedFDeriv ℝ n (fun w => chi w*F w) z‖ ≤ C n*M := by
  choose B hB HB using fun n:ℕ => hchic.exists_bound_iteratedFDeriv hchi n
  let C:ℕ→ℝ := fun n => (∑ i∈Finset.range (n+1),(n.choose i:ℝ)*B n)+1
  have hC:∀ n,0 < C n := by
    intro n
    dsimp only [C]
    have hh:0 ≤ ∑ i∈Finset.range (n+1),(n.choose i:ℝ)*B n :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hB n)
    linarith only [hh]
  refine ⟨C,hC,?_⟩
  intro F hF n M hM hBound z
  by_cases hz:z∈U
  · have hSmooth:=contDiff_product_cutoff_mul U hU chi hchi hchiU F hF
    have hcDer:∀ j:ℕ,iteratedFDerivWithin ℝ j chi U z=iteratedFDeriv ℝ j chi z :=
      fun j => iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
        (hchi.contDiffAt.of_le (by exact_mod_cast le_top)) hz
    have hFDer:∀ j:ℕ,iteratedFDerivWithin ℝ j F U z=iteratedFDeriv ℝ j F z :=
      fun j => iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
        ((hF.contDiffAt (hU.mem_nhds hz)).of_le (by exact_mod_cast le_top)) hz
    have hPDer:iteratedFDerivWithin ℝ n (fun w => chi w*F w) U z=iteratedFDeriv ℝ n (fun w => chi w*F w) z :=
      iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
        (hSmooth.contDiffAt.of_le (by exact_mod_cast le_top)) hz
    have hRaw:=norm_iteratedFDerivWithin_mul_le hchi.contDiffOn hF hU.uniqueDiffOn hz (n:=n) (by exact_mod_cast le_top)
    simp only [hcDer,hFDer,hPDer] at hRaw
    calc
      _ ≤ ∑ i∈Finset.range (n+1),(n.choose i:ℝ)*‖iteratedFDeriv ℝ i chi z‖*‖iteratedFDeriv ℝ (n-i) F z‖ := hRaw
      _ ≤ ∑ i∈Finset.range (n+1),(n.choose i:ℝ)*B n*M := by
        apply Finset.sum_le_sum
        intro i hi
        have hin:i ≤ n := by have hh:=Finset.mem_range.mp hi;omega
        exact mul_le_mul (mul_le_mul_of_nonneg_left (HB n i hin z) (Nat.cast_nonneg _))
          (hBound (n-i) (Nat.sub_le _ _) z hz) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB n))
      _ = (∑ i∈Finset.range (n+1),(n.choose i:ℝ)*B n)*M := (Finset.sum_mul _ _ _).symm
      _ ≤ C n*M := by dsimp only [C];nlinarith only [hM]
  · have hzOut:z∉tsupport chi := fun hh => hz (hchiU hh)
    have hzero:(fun w => chi w*F w)=ᶠ[𝓝 z] (fun _:R3×R3 => (0:ℝ)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzOut] with w hw
      simp only [hw,Pi.zero_apply,zero_mul]
    rw [(hzero.iteratedFDeriv ℝ n).eq_of_nhds]
    simpa only [iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero] using mul_nonneg (hC n).le hM

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
