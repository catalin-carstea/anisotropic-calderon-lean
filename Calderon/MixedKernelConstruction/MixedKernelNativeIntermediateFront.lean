import Calderon.MixedKernelConstruction.MixedKernelNativeCompactFront
import Calderon.MixedKernelConstruction.MixedKernelNativeGlobalEnergyDelta
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology InnerProductSpace

/-- Compactness of the ENTIRE tagged original front family over a positive closed delta band. -/
theorem isCompact_nativeSphereFront_parameter_band
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hRs : 0 < Rstar)
    (hRoom : ∀ d ∈ Icc delta (1 : ℝ), ∀ y ∈ cylinder,
      referenceRadius d Rstar p L y < C.radiusCeiling) :
    IsCompact {a : ℝ × (R3 × R3) | a.1 ∈ Icc delta (1 : ℝ) ∧
      a.2 ∈ nativeSphereFront S L C lam a.1 Rstar p} := by
  let K : Set (ℝ × (R3 × R3)) := Icc delta (1 : ℝ) ×ˢ (cylinder ×ˢ sphere (0 : R3) 1)
  let f : ℝ × (R3 × R3) → ℝ × (R3 × R3) := fun a =>
    (a.1,(nativeCoverEndpoint S L C lam
      ((a.2.1,referenceRadius a.1 Rstar p L a.2.1),a.2.2),a.2.1))
  have hK : IsCompact K := isCompact_Icc.prod
    (isCompact_cylinder.prod (isCompact_sphere (0 : R3) 1))
  have hf : ContinuousOn f K := by
    intro a ha
    have hdA : 0 < a.1 := hd.trans_le ha.1.1
    obtain ⟨i,hi⟩ := C.covers_cylinder a.2.1 ha.2.1
    have hz : ‖a.2.2‖ = 1 := by
      simpa only [mem_sphere,dist_zero_right] using ha.2.2
    have hr : ContinuousAt (fun b : ℝ × (R3 × R3) =>
        referenceRadius b.1 Rstar p L b.2.1) a := by
      have hPoint : (a.1,a.2.1) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set R3) := ⟨hdA,mem_univ _⟩
      have hOpen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set R3)) := isOpen_Ioi.prod isOpen_univ
      have hJoint : ContinuousAt (fun b : ℝ × R3 => referenceRadius b.1 Rstar p L b.2)
          (a.1,a.2.1) :=
        ((contDiffOn_referenceRadius_delta Rstar p L).contDiffAt (hOpen.mem_nhds hPoint)).continuousAt
      exact hJoint.comp (f := fun b : ℝ × (R3 × R3) => (b.1,b.2.1))
        (continuousAt_fst.prodMk continuousAt_snd.fst)
    have hMap : ContinuousAt (fun b : ℝ × (R3 × R3) =>
        ((b.2.1,referenceRadius b.1 Rstar p L b.2.1),b.2.2)) a :=
      (continuousAt_snd.fst.prodMk hr).prodMk continuousAt_snd.snd
    have hEnd : ContinuousAt (nativeCoverEndpoint S L C lam)
        ((a.2.1,referenceRadius a.1 Rstar p L a.2.1),a.2.2) :=
      (contDiffAt_nativeCoverEndpoint S L C lam hlam i a.2.1 hi
        (referenceRadius a.1 Rstar p L a.2.1)
        (referenceRadius_pos a.1 Rstar p L a.2.1 hdA hRs)
        (hRoom a.1 ha.1 a.2.1 ha.2.1) a.2.2 (by rw [hz];norm_num)).continuousAt
    exact (continuousAt_fst.prodMk
      ((hEnd.comp (f := fun b : ℝ × (R3 × R3) =>
        ((b.2.1,referenceRadius b.1 Rstar p L b.2.1),b.2.2)) hMap).prodMk continuousAt_snd.fst)).continuousWithinAt
  have hImage : f '' K = {a : ℝ × (R3 × R3) | a.1 ∈ Icc delta (1 : ℝ) ∧
      a.2 ∈ nativeSphereFront S L C lam a.1 Rstar p} := by
    ext a
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨hb.1,⟨b.2,hb.2,rfl⟩⟩
    · rintro ⟨ha,b,hb,hba⟩
      refine ⟨(a.1,b),⟨ha,hb⟩,?_⟩
      exact Prod.ext rfl hba
  rw [← hImage]
  exact hK.image_of_continuousOn hf

/-- The actual unseeded intermediate fronts have one COMPACT center room inside the SAME cylinder. -/
theorem exists_compact_native_unseeded_center_room
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hRs : 0 < Rstar)
    (hRoom : ∀ d ∈ Icc delta (1 : ℝ), ∀ y ∈ cylinder,
      referenceRadius d Rstar p L y < C.radiusCeiling)
    (Omega : Set (R3 × R3)) (hOmega : IsOpen Omega)
    (hBoundary : ∀ d ∈ Icc delta (1 : ℝ), ∀ q ∈ nativeSphereFront S L C lam d Rstar p,
      q.2 ∈ frontier cylinder → q ∈ Omega) :
    ∃ K : Set R3, IsCompact K ∧ K ⊆ interior cylinder ∧
      ∀ d ∈ Icc delta (1 : ℝ), ∀ q ∈ nativeSphereFront S L C lam d Rstar p,
        q ∉ Omega → q.2 ∈ K := by
  let A : Set (ℝ × (R3 × R3)) := {a | a.1 ∈ Icc delta (1 : ℝ) ∧
    a.2 ∈ nativeSphereFront S L C lam a.1 Rstar p}
  let U : Set (ℝ × (R3 × R3)) := A ∩ Prod.snd ⁻¹' Omegaᶜ
  let f : ℝ × (R3 × R3) → R3 := fun a => a.2.2
  have hA : IsCompact A := isCompact_nativeSphereFront_parameter_band S L C lam hlam
    delta Rstar p hd hRs hRoom
  have hU : IsCompact U := hA.inter_right (hOmega.isClosed_compl.preimage continuous_snd)
  refine ⟨f '' U,hU.image (continuous_snd.snd),?_,?_⟩
  · rintro y ⟨a,ha,rfl⟩
    have hCenter : a.2.2 ∈ cylinder := by
      obtain ⟨b,hb,hEq⟩ := ha.1.2
      have he : b.1 = a.2.2 := congrArg Prod.snd hEq
      exact he ▸ hb.1
    by_contra hInt
    have hFrontier : a.2.2 ∈ frontier cylinder := by
      change a.2.2 ∈ closure cylinder ∧ a.2.2 ∉ interior cylinder
      exact ⟨isClosed_cylinder.closure_eq.symm ▸ hCenter,hInt⟩
    exact ha.2 (hBoundary a.1 ha.1.1 a.2 ha.1.2 hFrontier)
  · intro d hD q hq hNo
    exact ⟨(d,q),⟨⟨hD,hq⟩,hNo⟩,rfl⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
