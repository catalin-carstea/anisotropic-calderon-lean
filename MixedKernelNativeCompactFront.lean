import MixedKernelCylinderBoundary
import Calderon.ActualScalarPrincipalAdjoint
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth ActualScalarPrincipalAdjoint
open scoped ContDiff Topology

/-- Selection is used only to represent the original coherent normal cover as one function. -/
def nativeCoverPacketIndex (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (y : R3) : Fin C.count := by
  classical
  exact if h : ∃ i, y ∈ (C.packet i).centers then h.choose else ⟨0,C.count_positive⟩

/-- The endpoint is literally one original packet endpoint; overlap coherence removes the choice. -/
def nativeCoverEndpoint (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (a : (R3 × ℝ) × R3) : R3 :=
  packetEndpoint S L (C.packet (nativeCoverPacketIndex S L C a.1.1)) lam a.1.1 a.1.2 a.2

/-- Every original packet represents this endpoint on its entire actual common room. -/
theorem nativeCoverEndpoint_eq_packet (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (i : Fin C.count) (y : R3) (hy : y ∈ (C.packet i).centers)
    (r : ℝ) (hr : 0 < r) (hsmall : r < C.radiusCeiling)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    nativeCoverEndpoint S L C lam ((y,r),z) = packetEndpoint S L (C.packet i) lam y r z := by
  classical
  have h : ∃ j, y ∈ (C.packet j).centers := ⟨i,hy⟩
  have hc : y ∈ (C.packet (nativeCoverPacketIndex S L C y)).centers := by
    simpa only [nativeCoverPacketIndex,dif_pos h] using h.choose_spec
  exact C.endpoint_coherence (nativeCoverPacketIndex S L C y) i lam hlam y ⟨hc,hy⟩ r hr hsmall z hz

/-- Local smoothness is obtained from actual overlap equality, without a smooth index choice. -/
theorem contDiffAt_nativeCoverEndpoint (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (i : Fin C.count) (y : R3) (hy : y ∈ (C.packet i).centers)
    (r : ℝ) (hr : 0 < r) (hsmall : r < C.radiusCeiling) (z : R3) (hz : ‖z‖ < 2) :
    ContDiffAt ℝ ∞ (nativeCoverEndpoint S L C lam) ((y,r),z) := by
  let P := C.packet i
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) :=
    hEnd.2.2.2.2.2.2.2.1
  have hSmooth : ContDiff ℝ ∞ (fun a : (R3 × ℝ) × R3 => packetEndpoint S L P lam a.1.1 a.1.2 a.2) :=
    (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk contDiff_id)
  have hcent : ∀ᶠ a : (R3 × ℝ) × R3 in 𝓝 ((y,r),z), a.1.1 ∈ P.centers :=
    (continuousAt_fst.fst).eventually (P.centers_open.mem_nhds hy)
  have hrad : ∀ᶠ a : (R3 × ℝ) × R3 in 𝓝 ((y,r),z), a.1.2 ∈ Ioo (0 : ℝ) C.radiusCeiling :=
    (continuousAt_fst.snd).eventually (isOpen_Ioo.mem_nhds ⟨hr,hsmall⟩)
  have hspatial : ∀ᶠ a : (R3 × ℝ) × R3 in 𝓝 ((y,r),z), a.2 ∈ ball (0 : R3) 2 :=
    continuousAt_snd.eventually (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_zero_right] using hz))
  have hEq : nativeCoverEndpoint S L C lam =ᶠ[𝓝 ((y,r),z)]
      (fun a : (R3 × ℝ) × R3 => packetEndpoint S L P lam a.1.1 a.1.2 a.2) := by
    filter_upwards [hcent,hrad,hspatial] with a hc ha hz'
    exact nativeCoverEndpoint_eq_packet S L C lam hlam i a.1.1 hc a.1.2 ha.1 ha.2 a.2
      (ball_subset_closedBall hz')
  exact hSmooth.contDiffAt.congr_of_eventuallyEq hEq

/-- The full native sphere family, with no cylinder boundary or packet omitted. -/
def nativeSphereFront (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam delta Rstar : ℝ) (p : ℕ) : Set (R3 × R3) :=
  (fun a : R3 × R3 =>
    (nativeCoverEndpoint S L C lam ((a.1,referenceRadius delta Rstar p L a.1),a.2),a.1)) ''
      (cylinder ×ˢ sphere (0 : R3) 1)

/-- Compactness uses the literal closed cylinder, not its open packet pieces. -/
theorem isCompact_cylinder : IsCompact cylinder :=
  (isCompact_closedBall (0 : R3) 2).of_isClosed_subset isClosed_cylinder
    (fun y hy => by simpa only [mem_closedBall,dist_zero_right] using norm_le_two_of_mem_cylinder y hy)

/-- The entire actual native sphere front is compact. -/
theorem isCompact_nativeSphereFront (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hR : 0 < Rstar)
    (hroom : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < C.radiusCeiling) :
    IsCompact (nativeSphereFront S L C lam delta Rstar p) := by
  apply (isCompact_cylinder.prod (isCompact_sphere (0 : R3) 1)).image_of_continuousOn
  intro a ha
  obtain ⟨i,hi⟩ := C.covers_cylinder a.1 ha.1
  have hz : ‖a.2‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using ha.2
  have hmap : ContinuousAt (fun b : R3 × R3 => ((b.1,referenceRadius delta Rstar p L b.1),b.2)) a :=
    (continuousAt_fst.prodMk ((contDiff_referenceRadius_actual delta Rstar p L hd hR).continuous.continuousAt.comp
      continuousAt_fst)).prodMk continuousAt_snd
  have hNative : ContinuousAt (nativeCoverEndpoint S L C lam)
      ((a.1,referenceRadius delta Rstar p L a.1),a.2) :=
    (contDiffAt_nativeCoverEndpoint S L C lam hlam i a.1 hi
      (referenceRadius delta Rstar p L a.1) (referenceRadius_pos delta Rstar p L a.1 hd hR)
      (hroom a.1 ha.1) a.2 (by rw [hz];norm_num)).continuousAt
  have hEnd : ContinuousAt (fun b : R3 × R3 =>
      nativeCoverEndpoint S L C lam ((b.1,referenceRadius delta Rstar p L b.1),b.2)) a :=
    hNative.comp (f := fun b : R3 × R3 =>
      ((b.1,referenceRadius delta Rstar p L b.1),b.2)) hmap
  exact (hEnd.prodMk continuousAt_fst).continuousWithinAt

/-- Every original packet's actual pair lies in the same compact front. -/
theorem packet_referenceRadius_pair_mem_nativeSphereFront
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hR : 0 < Rstar)
    (i : Fin C.count) (y : R3) (hy : y ∈ cylinder ∩ (C.packet i).centers)
    (z : R3) (hz : z ∈ sphere (0 : R3) 1)
    (hroom : referenceRadius delta Rstar p L y < C.radiusCeiling) :
    (packetEndpoint S L (C.packet i) lam y (referenceRadius delta Rstar p L y) z,y) ∈
      nativeSphereFront S L C lam delta Rstar p := by
  refine ⟨(y,z),⟨hy.1,hz⟩,?_⟩
  have hz2 : z ∈ closedBall (0 : R3) 2 := by
    have hh : ‖z‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hz
    simp only [mem_closedBall,dist_zero_right,hh]
    norm_num
  exact congrArg (fun X : R3 => (X,y)) (nativeCoverEndpoint_eq_packet S L C lam hlam i y hy.2
    (referenceRadius delta Rstar p L y) (referenceRadius_pos delta Rstar p L y hd hR) hroom z hz2)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
