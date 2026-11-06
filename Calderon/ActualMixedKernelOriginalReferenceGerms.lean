import Calderon.ActualMixedKernelPhysicalDensityRepresentation

set_option autoImplicit false
noncomputable section
open Set Metric Filter Function
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ExteriorSource ConnectionError ConformalDepth

theorem original_reference_kernel_eventuallyEq_reciprocal_same_mixed_datum
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hlam : 0 < lam) (i : Fin cover.count) (y : R3)
    (hy : y ∈ cylinder ∩ (cover.packet i).centers) (hKnown : lam • y ∈ S.W)
    (Gext : R3 × R3 → ℝ)
    (hGerm : ∀ theta ∈ sphere (0 : R3) 1, Gext =ᶠ[𝓝 (packetEndpoint S L (cover.packet i)
      lam y (referenceRadius delta Rstar p L y) theta,y)] K.kernel)
    (Fext : R3 → R3)
    (hFNear : ∀ theta ∈ sphere (0 : R3) 1, Fext =ᶠ[𝓝 theta]
      (fun z => S.Xi1 (lam • packetEndpoint S L (cover.packet i) lam y
        (referenceRadius delta Rstar p L y) z)))
    (pole : (radiusTwoOpens : Set R3)) (hPole : (pole : R3) = S.Xi1 (lam • y)) :
    ∀ theta ∈ sphere (0 : R3) 1,
      (fun z => lam⁻¹ * Gext (packetEndpoint S L (cover.packet i) lam y
        (referenceRadius delta Rstar p L y) z,y)) =ᶠ[𝓝 theta]
      (fun z => S.G1 pole (Fext z)) := by
  let P := cover.packet i
  let X : R3 → R3 := packetEndpoint S L P lam y (referenceRadius delta Rstar p L y)
  have hTheta : ContDiff ℝ ∞ (fun v : ℝ × (R3 × R3) => (P.Phi v.1 v.2 1).1) :=
    P.native_data.1.1.1.2.2.2.2.2.2.2.1
  have hX : Continuous X :=
    ((contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))).continuous
  have hPoleEq : (⟨S.Xi1 (lam • y),S.Xi1_room (lam • y) (S.W_room hKnown)⟩ :
      (radiusTwoOpens : Set R3)) = pole := Subtype.ext hPole.symm
  intro theta ht
  have hMap : Tendsto (fun z => (X z,y)) (𝓝 theta) (𝓝 (X theta,y)) :=
    (hX.continuousAt.prodMk continuousAt_const).tendsto
  have hE : (fun z => Gext (X z,y)) =ᶠ[𝓝 theta] (fun z => K.kernel (X z,y)) :=
    (hGerm theta ht).comp_tendsto hMap
  have hRoom : IsOpen ((fun z => (X z,y)) ⁻¹' K.domain) :=
    K.domain_open.preimage (hX.prodMk continuous_const)
  have hAt : theta ∈ (fun z => (X z,y)) ⁻¹' K.domain := K.sphere_cover i y hy theta ht
  have hK : (fun z => K.kernel (X z,y)) =ᶠ[𝓝 theta]
      (fun z => lam * S.G1 pole (S.Xi1 (lam • X z))) := by
    filter_upwards [hRoom.mem_nhds hAt] with z hz
    rw [K.first_lower_cross (X z,y) hz hKnown]
    simp only [dilatedKernel1,coordinateKernel1,dif_pos (S.W_room hKnown),hPoleEq]
  have hF : (fun z => lam * S.G1 pole (S.Xi1 (lam • X z))) =ᶠ[𝓝 theta]
      (fun z => lam * S.G1 pole (Fext z)) :=
    (hFNear theta ht).symm.mono (fun z hz => congrArg (fun w => lam * S.G1 pole w) hz)
  have hAll := hE.trans (hK.trans hF)
  filter_upwards [hAll] with z hz
  change lam⁻¹ * Gext (X z,y) = S.G1 pole (Fext z)
  rw [hz,← mul_assoc,inv_mul_cancel₀ hlam.ne',one_mul]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
