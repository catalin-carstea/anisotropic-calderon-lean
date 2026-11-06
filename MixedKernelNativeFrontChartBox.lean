import MixedKernelActualChartZeroBox
import MixedKernelNativeRadialCoordinates
import MixedKernelNativeRadialSeedBoundary
import MixedKernelNativeFrontLocalExtension
import MixedKernelCompactLevelGluing
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology InnerProductSpace

/-- The genuine local native PDE output can be chosen in SAME-chart boxes with both complete lower crosses. -/
theorem exists_native_front_chart_box_with_full_crosses
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling) (hlamPos : 0<lam)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta Rstar : ℝ) (hd : 0<delta) (hRs : 0<Rstar) (p : ℕ)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y<R)
    (q : R3 × R3) (hq : q ∈ nativeSphereFront S L C lam delta Rstar p)
    (hy : q.2 ∈ interior cylinder)
    (hTest : ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun y => S.g2 (lam • y))
      q.1 q.2 (nativeGlobalEnergy S L C lam R delta Rstar p))
    (F : R3 × R3 → ℝ)
    (hF : ProductSolutionOn S L lam F (nativeRadialOutsideRoom S L C lam R delta Rstar p))
    (hF1 : ∀ v ∈ nativeRadialOutsideRoom S L C lam R delta Rstar p,
      lam • v.2 ∈ S.W → F v=dilatedKernel1 S lam v)
    (hF2 : ∀ v ∈ nativeRadialOutsideRoom S L C lam R delta Rstar p,
      lam • v.1 ∈ S.W → F v=dilatedKernel2 S lam v) :
    let e := nativeEnergyRadialChart S L C lam hlam R hR hRoom delta Rstar p hd hRs
    ∃ B : Set (R3 × sphere (0 : R3) 1), IsOpen B ∧ (e q).1 ∈ B ∧
      ∃ d : ℝ, 0<d ∧ B ×ˢ Ioo (-d) d ⊆ e.target ∧
        ∃ G : R3 × R3 → ℝ,
          let V := e.source ∩ e ⁻¹' (B ×ˢ Ioo (-d) d)
          q ∈ V ∧ V ⊆ dilatedOffDiagonal S lam ∧ ProductSolutionOn S L lam G V ∧
            (∀ v ∈ V, 0<(e v).2 → G v=F v) ∧
            (∀ v ∈ V, lam • v.2 ∈ S.W → G v=dilatedKernel1 S lam v) ∧
            (∀ v ∈ V, lam • v.1 ∈ S.W → G v=dilatedKernel2 S lam v) := by
  intro e
  have hqN := nativeSphereFront_subset_nativeNormalImage S L C lam hlam R hR hRoom
    delta Rstar hd hRs p hRadius hq
  have hNorm := nativeVelocityInverse_norm_on_nativeSphereFront S L C lam hlam R hR hRoom
    delta Rstar p hd hRs hRadius q hq
  have hqNe : (nativeVelocityInverse S L C lam R q).2≠0 := by
    apply norm_pos_iff.mp
    rw [hNorm]
    exact referenceRadius_pos delta Rstar p L q.2 hd hRs
  have hqSource : q ∈ e.source := by
    rw [nativeEnergyRadialChart_source]
    exact ⟨hqN,hqNe⟩
  have hzero : (e q).2=0 := by
    rw [nativeEnergyRadialChart_height S L C lam hlam R hR hRoom delta Rstar p hd hRs q hqN hqNe,hNorm,sub_self]
  obtain ⟨V0,G,hV0,hqV0,hVRoom,hG,hEq,hG1,hG2⟩ :=
    exists_native_front_local_extension_with_full_crosses S L C lam hlam hlamPos R hR hRoom
      delta Rstar hd hRs p hRadius q hq hy hTest F hF hF1 hF2
  let V1 : Set (R3 × R3) := V0 ∩ {v | v.2 ∈ interior cylinder}
  have hV1 : IsOpen V1 := hV0.inter (isOpen_interior.preimage continuous_snd)
  obtain ⟨B,hB,hbase,d,hD,hTarget,hSub⟩ :=
    exists_actual_chart_zero_box e q hqSource hzero V1 hV1 ⟨hqV0,hy⟩
  let V := e.source ∩ e ⁻¹' (B ×ˢ Ioo (-d) d)
  have hVV0 : V ⊆ V0 := fun v hv => (hSub hv).1
  have hqV : q ∈ V := ⟨hqSource,hbase,by rw [hzero];exact ⟨by linarith, hD⟩⟩
  refine ⟨B,hB,hbase,d,hD,hTarget,G,hqV,hVV0.trans hVRoom,
    productSolutionOn_mono hG hVV0,?_,?_,?_⟩
  · intro v hv hPos
    have hSource := hv.1
    rw [nativeEnergyRadialChart_source] at hSource
    have hE : 0<nativeGlobalEnergy S L C lam R delta Rstar p v :=
      (nativeGlobalEnergy_pos_iff_nativeEnergyRadialChart_height_pos S L C lam hlam R hR hRoom
        delta Rstar p hd hRs v hSource.1 hSource.2).mpr hPos
    have hOld : v ∈ nativeRadialOutsideRoom S L C lam R delta Rstar p := by
      rw [nativeRadialOutsideRoom_eq_positive_nativeGlobalEnergy S L C lam hlam R hR hRoom delta Rstar hd hRs p]
      exact ⟨hSource.1,(hSub hv).2,hE⟩
    exact hEq ⟨hVV0 hv,hOld⟩
  · intro v hv
    exact hG1 v (hVV0 hv)
  · intro v hv
    exact hG2 v (hVV0 hv)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
