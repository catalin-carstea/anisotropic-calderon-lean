import Calderon.MixedKernelConstruction.MixedKernelCurrentBootstrapMonotone
import Calderon.MixedKernelConstruction.MixedKernelNativeGlobalEnergyDelta
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology

/-- The SAME genuine outside domains have the exact reversed original delta order. -/
theorem nativeRadialOutsideRoom_mono_delta
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam R delta delta' Rstar : ℝ) (p : ℕ)
    (hd : 0 < delta) (hle : delta ≤ delta') (hRs : 0 ≤ Rstar) :
    nativeRadialOutsideRoom S L C lam R delta' Rstar p ⊆
      nativeRadialOutsideRoom S L C lam R delta Rstar p := by
  rintro q ⟨a,ha,rfl⟩
  exact ⟨a,⟨ha.1,(referenceRadius_mono_delta delta delta' Rstar p L a.1 hd hle hRs).trans_lt ha.2.1,
    ha.2.2⟩,rfl⟩

/-- At an intermediate last level, the ACTUAL strict outside is the union of already higher-delta outsides. -/
theorem nativeRadialOutsideRoom_eq_iUnion_larger_delta
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam R delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hd1 : delta < 1) (hRs : 0 ≤ Rstar) :
    nativeRadialOutsideRoom S L C lam R delta Rstar p =
      ⋃ d ∈ Ioc delta (1 : ℝ), nativeRadialOutsideRoom S L C lam R d Rstar p := by
  apply subset_antisymm
  · rintro q ⟨a,ha,rfl⟩
    have hRadius : ContinuousAt (fun d : ℝ => referenceRadius d Rstar p L a.1) delta := by
      have hPoint : (delta,a.1) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set R3) := ⟨hd,mem_univ _⟩
      have hOpen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set R3)) := isOpen_Ioi.prod isOpen_univ
      have hh : ContinuousAt (fun b : ℝ × R3 => referenceRadius b.1 Rstar p L b.2)
          (delta,a.1) :=
        ((contDiffOn_referenceRadius_delta Rstar p L).contDiffAt (hOpen.mem_nhds hPoint)).continuousAt
      exact hh.comp (f := fun d : ℝ => (d,a.1)) (continuousAt_id.prodMk continuousAt_const)
    have hNear : {d : ℝ | referenceRadius d Rstar p L a.1 < ‖a.2‖} ∈ 𝓝 delta :=
      hRadius.preimage_mem_nhds (Iio_mem_nhds ha.2.1)
    obtain ⟨eps,heps,hBall⟩ := Metric.mem_nhds_iff.mp hNear
    let h := min eps (1-delta)/2
    have hPos : 0 < h := div_pos (lt_min heps (by linarith)) (by norm_num)
    have hEps : h < eps := by
      have hh : h ≤ eps/2 := div_le_div_of_nonneg_right (min_le_left eps (1-delta)) (by norm_num)
      linarith
    have hOne : delta+h ≤ 1 := by
      have hh : h ≤ (1-delta)/2 := div_le_div_of_nonneg_right (min_le_right eps (1-delta)) (by norm_num)
      linarith
    have hMem : delta+h ∈ Metric.ball delta eps := by
      rw [Metric.mem_ball,Real.dist_eq]
      have hh : delta+h-delta=h := by ring
      rw [hh,abs_of_pos hPos]
      exact hEps
    refine mem_iUnion.mpr ⟨delta+h,mem_iUnion.mpr ⟨⟨by linarith,hOne⟩,?_⟩⟩
    exact ⟨a,⟨ha.1,hBall hMem,ha.2.2⟩,rfl⟩
  · intro q hq
    obtain ⟨d,hd',hq'⟩ := mem_iUnion₂.mp hq
    exact nativeRadialOutsideRoom_mono_delta S L C lam R delta d Rstar p hd hd'.1.le hRs hq'

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
