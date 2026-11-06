import MixedKernelNativeNormalDomain
import MixedKernelNativeEnergyOutside
import MixedKernelFullCrossExtension
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology

/-- The literal global native energy extends an ACTUAL outside solution at an unseeded interior front point. -/
theorem exists_native_front_local_extension_with_full_crosses
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling) (hlamPos : 0 < lam)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta Rstar : ℝ) (hd : 0 < delta) (hRs : 0 < Rstar) (p : ℕ)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < R)
    (q : R3 × R3) (hq : q ∈ nativeSphereFront S L C lam delta Rstar p)
    (hy : q.2 ∈ interior cylinder)
    (hTest : ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun y => S.g2 (lam • y))
      q.1 q.2 (nativeGlobalEnergy S L C lam R delta Rstar p))
    (F : R3 × R3 → ℝ)
    (hF : ProductSolutionOn S L lam F (nativeRadialOutsideRoom S L C lam R delta Rstar p))
    (hF1 : ∀ v ∈ nativeRadialOutsideRoom S L C lam R delta Rstar p,
      lam • v.2 ∈ S.W → F v = dilatedKernel1 S lam v)
    (hF2 : ∀ v ∈ nativeRadialOutsideRoom S L C lam R delta Rstar p,
      lam • v.1 ∈ S.W → F v = dilatedKernel2 S lam v) :
    ∃ (V : Set (R3 × R3)) (G : R3 × R3 → ℝ), IsOpen V ∧ q ∈ V ∧
      V ⊆ dilatedOffDiagonal S lam ∧ ProductSolutionOn S L lam G V ∧
      EqOn G F (V ∩ nativeRadialOutsideRoom S L C lam R delta Rstar p) ∧
      (∀ v ∈ V, lam • v.2 ∈ S.W → G v = dilatedKernel1 S lam v) ∧
      (∀ v ∈ V, lam • v.1 ∈ S.W → G v = dilatedKernel2 S lam v) := by
  let E := nativeGlobalEnergy S L C lam R delta Rstar p
  let U : Set (R3 × R3) :=
    (nativeNormalImage S L C lam R ∩ {v | v.1 ≠ v.2}) ∩ {v | v.2 ∈ interior cylinder}
  have hU : IsOpen U := ((isOpen_nativeNormalImage S L C lam hlam R hR hRoom).inter
    (isOpen_ne_fun continuous_fst continuous_snd)).inter (isOpen_interior.preimage continuous_snd)
  have hqN := nativeSphereFront_subset_nativeNormalImage S L C lam hlam R hR hRoom
    delta Rstar hd hRs p hRadius hq
  have hqD := nativeSphereFront_subset_dilatedOffDiagonal S L C lam hlam R hR hRoom
    delta Rstar hd hRs p hRadius hq
  have hqU : q ∈ U := ⟨⟨hqN,hqD.2.2⟩,hy⟩
  have hURoom : U ⊆ dilatedOffDiagonal S lam := by
    intro v hv
    obtain ⟨hx,hy'⟩ := nativeNormalImage_coordinate_rooms S L C lam hlam R hR hRoom v hv.1.1
    exact ⟨hx,hy',hv.1.2⟩
  have hSmooth : ContDiffOn ℝ ∞ E U :=
    (contDiffOn_nativeGlobalEnergy S L C lam hlam R hR hRoom delta Rstar hd hRs p).mono
      (fun v hv => hv.1.1)
  have hZero : E q = 0 := nativeGlobalEnergy_zero_on_nativeSphereFront S L C lam hlam R hR hRoom
    delta Rstar hd hRs p hRadius q hq
  have hOld : {v : R3 × R3 | v ∈ U ∧ 0 < E v} ⊆
      nativeRadialOutsideRoom S L C lam R delta Rstar p := by
    intro v hv
    rw [nativeRadialOutsideRoom_eq_positive_nativeGlobalEnergy S L C lam hlam R hR hRoom
      delta Rstar hd hRs p]
    exact ⟨hv.1.1.1,hv.1.2,hv.2⟩
  obtain ⟨V,G,hV,hqV,hVU,hG,hEq,h1,h2⟩ :=
    exists_product_solution_extension_with_full_crosses S L lam hlamPos q.1 q.2 U hU hqU hURoom
      E hSmooth hZero hTest F (productSolutionOn_mono hF hOld)
      (fun v hv hpos => hF1 v (hOld ⟨hv,hpos⟩))
      (fun v hv hpos => hF2 v (hOld ⟨hv,hpos⟩))
  refine ⟨V,G,hV,hqV,hVU.trans hURoom,hG,?_,h1,h2⟩
  intro v hv
  have hOutside := hv.2
  rw [nativeRadialOutsideRoom_eq_positive_nativeGlobalEnergy S L C lam hlam R hR hRoom
    delta Rstar hd hRs p] at hOutside
  exact hEq ⟨hv.1,hVU hv.1,hOutside.2.2⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
