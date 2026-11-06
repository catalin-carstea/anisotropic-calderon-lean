import Calderon.ActualMixedKernelPhysicalDensityRepresentation

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Distributions InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ExteriorSource ConnectionError MetricVolume MetricOperator ReferenceWeightedApproximation ConformalDepth

/-- The original inverse source retains its exact Lebesgue point-source normalization. -/
theorem original_first_kernel_pointSource (S : KnownSideSourceData)
    (pole : (radiusTwoOpens : Set R3)) (phi : 𝓓(radiusTwoOpens,ℝ)) :
    (∫ z in radiusTwoOpens, S.G1 pole z *
      (radiusTwoCompactMetricTestDensity S.original1 S.original1_admissible phi).1 z
      ∂(volume : Measure R3)) = phi (pole : R3) := by
  exact (S.kernel1.1.1 pole).2.2.2.2.2 phi

/-- The actual framed endpoint puts the reference origin at the SAME physical center. -/
theorem packetEndpoint_zero_eq_center
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : y ∈ P.centers) (r : ℝ) :
    packetEndpoint S L P lam y r 0 = y := by
  unfold packetEndpoint referenceFramedPhysicalEndpoint
  simp only [map_zero,smul_zero]
  exact P.native_data.1.1.1.2.2.2.2.2.2.2.2.1 lam hlam y (P.centers_room y hy).2

/-- Matching on the original known side supplies FULL product germs, hence exact signed flux. -/
theorem nativeMixedKernelWronskianFlux_eq_first_kernel_on_known_side
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (i : Fin cover.count) (y : R3) (hy : y ∈ cylinder ∩ (cover.packet i).centers)
    (u : R3 → ℝ) (hknown : lam • y ∈ S.W) :
    nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u
      y (referenceRadius delta Rstar p L y) y =
    nativeMixedKernelWronskianFlux S L (cover.packet i) lam (dilatedKernel1 S lam) u
      y (referenceRadius delta Rstar p L y) y := by
  apply nativeMixedKernelWronskianFlux_eq_of_product_germs
  intro z hz
  let V : Set (R3 × R3) := K.domain ∩ (fun v : R3 × R3 => lam • v.2) ⁻¹' S.W
  have hMap : Continuous (fun v : R3 × R3 => lam • v.2) :=
    (continuous_snd : Continuous (fun v : R3 × R3 => v.2)).const_smul lam
  have hV : IsOpen V := K.domain_open.inter (S.W_open.preimage hMap)
  have hAt : (packetEndpoint S L (cover.packet i) lam y
      (referenceRadius delta Rstar p L y) z,y) ∈ V :=
    ⟨K.sphere_cover i y hy z hz,hknown⟩
  filter_upwards [hV.mem_nhds hAt] with v hv
  exact K.first_lower_cross v hv.1 hv.2

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
