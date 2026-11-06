import MixedKernelNativeFrontChartBox
import MixedKernelNativeFullCrossLevelGluing
import MixedKernelNativeReachedLevel
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology InnerProductSpace

/-- Exact packet/cover coherence turns actual packet tests into strictness on the ENTIRE original native front. -/
theorem nativeSphereFront_strict_of_packet_tests
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (c Rstar : ℝ) (p : ℕ) (hc : 0<c) (hRs : 0<Rstar)
    (hRadius : ∀ y ∈ cylinder, referenceRadius c Rstar p L y<R)
    (hTest : ∀ (i : Fin C.count) (y : R3), y ∈ cylinder ∩ (C.packet i).centers →
      ∀ z : R3, ‖z‖=1 →
        ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun y => S.g2 (lam • y))
          (packetEndpoint S L (C.packet i) lam y (referenceRadius c Rstar p L y) z) y
          (nativeGlobalEnergy S L C lam R c Rstar p)) :
    ∀ q ∈ nativeSphereFront S L C lam c Rstar p,
      ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun y => S.g2 (lam • y))
        q.1 q.2 (nativeGlobalEnergy S L C lam R c Rstar p) := by
  rintro q ⟨a,ha,rfl⟩
  obtain ⟨i,hi⟩ := C.covers_cylinder a.1 ha.1
  have hz : ‖a.2‖=1 := by simpa only [mem_sphere,dist_zero_right] using ha.2
  have hBall : a.2 ∈ closedBall (0 : R3) 2 := by
    simp only [mem_closedBall,dist_zero_right,hz]
    norm_num
  change ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun y => S.g2 (lam • y))
    (nativeCoverEndpoint S L C lam ((a.1,referenceRadius c Rstar p L a.1),a.2)) a.1
    (nativeGlobalEnergy S L C lam R c Rstar p)
  rw [nativeCoverEndpoint_eq_packet S L C lam hlam i a.1 hi
    (referenceRadius c Rstar p L a.1) (referenceRadius_pos c Rstar p L a.1 hc hRs)
    ((hRadius a.1 ha.1).trans hRoom) a.2 hBall]
  exact hTest i a.1 ⟨ha.1,hi⟩ a.2 hz

/-- An ACTUAL old-side kernel extends to a genuine open collar of the ENTIRE native front, retaining SAME seed and BOTH full crosses. -/
theorem native_reached_of_canonical_solution
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling) (hlamPos : 0<lam)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (c Rstar tail : ℝ) (p : ℕ) (hc : 0<c) (hRs : 0<Rstar)
    (hRadius : ∀ y ∈ cylinder, referenceRadius c Rstar p L y<R)
    (hBoundary : ∀ q ∈ nativeSphereFront S L C lam c Rstar p,
      q.2 ∈ frontier cylinder → q ∈ nativeRadialSeedRoom S L C lam R tail)
    (hStrict : ∀ q ∈ nativeSphereFront S L C lam c Rstar p,
      ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun y => S.g2 (lam • y))
        q.1 q.2 (nativeGlobalEnergy S L C lam R c Rstar p))
    (Hseed F : R3 × R3 → ℝ)
    (hOld : ProductSolutionOn S L lam F (nativeRadialCanonicalRoom S L C lam R c Rstar tail p))
    (hOldEq : EqOn F Hseed (nativeRadialSeedRoom S L C lam R tail))
    (hOld1 : ∀ q ∈ nativeRadialCanonicalRoom S L C lam R c Rstar tail p,
      lam • q.2 ∈ S.W → F q=dilatedKernel1 S lam q)
    (hOld2 : ∀ q ∈ nativeRadialCanonicalRoom S L C lam R c Rstar tail p,
      lam • q.1 ∈ S.W → F q=dilatedKernel2 S lam q) :
    NativeReachedAt S L C lam R Rstar tail p Hseed c := by
  classical
  let e := nativeEnergyRadialChart S L C lam hlam R hR hRoom c Rstar p hc hRs
  let A := nativeRadialCanonicalRoom S L C lam R c Rstar tail p
  let I := {q : R3 × R3 // q ∈ nativeSphereFront S L C lam c Rstar p ∧
    q ∉ nativeRadialSeedRoom S L C lam R tail}
  have hInterior (i : I) : i.1.2 ∈ interior cylinder := by
    have hCyl : i.1.2 ∈ cylinder := by
      obtain ⟨u,hu,hUq⟩ := i.2.1
      have hh : u.1=i.1.2 := congrArg Prod.snd hUq
      exact hh ▸ hu.1
    by_contra hNo
    have hFront : i.1.2 ∈ frontier cylinder := by
      change i.1.2 ∈ closure cylinder ∧ i.1.2 ∉ interior cylinder
      exact ⟨isClosed_cylinder.closure_eq.symm ▸ hCyl,hNo⟩
    exact i.2.2 (hBoundary i.1 i.2.1 hFront)
  have hExt (i : I) := exists_native_front_chart_box_with_full_crosses S L C lam hlam hlamPos R hR hRoom
    c Rstar hc hRs p hRadius i.1 i.2.1 (hInterior i) (hStrict i.1 i.2.1) F
    (productSolutionOn_mono hOld (fun q hq => Or.inr hq))
    (fun q hq => hOld1 q (Or.inr hq)) (fun q hq => hOld2 q (Or.inr hq))
  dsimp only at hExt
  choose B hB hBase d hd hTarget G hPoint hRoomG hSolG hEqG hCross1 hCross2 using hExt
  let V : I → Set (R3 × R3) := fun i => e.source ∩ e ⁻¹' (B i ×ˢ Ioo (-(d i)) (d i))
  have hASource : A ⊆ e.source :=
    nativeRadialCanonicalRoom_subset_radial_source S L C lam hlam R hR hRoom
      c c Rstar tail p hc hc hRs
  have hARoom : A ⊆ dilatedOffDiagonal S lam := by
    intro q hq
    have hs := hASource hq
    rw [nativeEnergyRadialChart_source] at hs
    exact nativeNormalImage_mem_dilatedOffDiagonal_of_velocity_ne_zero S L C lam hlam R hR hRoom q hs.1 hs.2
  have hAOpen : IsOpen A := isOpen_nativeRadialCanonicalRoom S L C lam hlam R hR hRoom c Rstar tail p hc hRs
  have hUp : ∀ q ∈ A ∩ e.source, ∀ t : ℝ, (e q).2≤t → ((e q).1,t) ∈ e.target → e.symm ((e q).1,t) ∈ A := by
    intro q hq t hle ht
    rcases hq.1 with hs | ho
    · exact Or.inl (nativeRadialSeedRoom_upward_in_nativeEnergyRadialChart S L C lam hlam R hR hRoom
        c Rstar tail p hc hRs q ⟨hs,hq.2⟩ t hle ht)
    · exact Or.inr (nativeRadialOutsideRoom_upward_in_nativeEnergyRadialChart S L C lam hlam R hR hRoom
        c c Rstar p hc hc hRs q ⟨ho,hq.2⟩ t hle ht)
  have hGlue := exists_native_full_cross_solution_from_common_level_boxes S L lam e B hB 0 d hd
    (fun i => by simpa only [zero_sub,zero_add] using hTarget i)
    A hAOpen hARoom hUp F hOld hOld1 hOld2 G
    (fun i => by simpa only [zero_sub,zero_add] using hSolG i)
    (fun i => by simpa only [zero_sub,zero_add] using hRoomG i)
    (fun i => by simpa only [zero_sub,zero_add] using hCross1 i)
    (fun i => by simpa only [zero_sub,zero_add] using hCross2 i)
    (fun i => by simpa only [zero_sub,zero_add] using hEqG i)
  dsimp only at hGlue
  simp only [zero_sub,zero_add] at hGlue
  obtain ⟨hMOpen,hMRoom,H,hHSol,hHF,hHG,hH1,hH2⟩ := hGlue
  let M : Set (R3 × R3) := A ∪ ⋃ i, V i
  have hMSource : M ⊆ nativeNonzeroNormalImage S L C lam R := by
    intro q hq
    have hs : q ∈ e.source := by
      rcases hq with ha | hv
      · exact hASource ha
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hv
        exact hi.1
    rw [nativeEnergyRadialChart_source] at hs
    exact hs
  have hFront : nativeSphereFront S L C lam c Rstar p ⊆ M := by
    intro q hq
    by_cases hSeed : q ∈ nativeRadialSeedRoom S L C lam R tail
    · exact Or.inl (Or.inl hSeed)
    · let i : I := ⟨q,hq,hSeed⟩
      exact Or.inr (mem_iUnion.mpr ⟨i,hPoint i⟩)
  refine ⟨M,H,hMOpen,hMSource,fun q hq => Or.inl (Or.inl hq),
    fun q hq => Or.inl (Or.inr hq),hFront,hHSol,?_,hH1,hH2⟩
  intro q hq
  exact (hHF (Or.inl hq)).trans (hOldEq hq)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
