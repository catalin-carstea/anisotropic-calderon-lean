import Calderon.ActualEligibleDensityWholeCoverOutput
set_option autoImplicit false
noncomputable section
open Set
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ActualFiniteHarmonicCore ConformalDepth
attribute [local irreducible] sphereSobolevInclusionL harmonicSphereSubspace

theorem eq_of_same_native_cover_negative_graph
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (S:KnownSideSourceData) (L:ℝ) (cover:NativeNormalCover S L)
    (K:Set R3) (hK:K⊆interior cylinder)
    (f W:R3→SphereL2) (hf:tsupport f⊆K) (hW:tsupport W⊆K)
    (Q:Fin cover.count→R3→SphereSobolev (-(1/2:ℝ)))
    (hFGraph:∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (f y))=Q i y)
    (hWGraph:∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (W y))=Q i y):
    f=W := by
  funext y
  by_cases hy:y∈K
  · obtain ⟨i,hi⟩ := cover.covers_cylinder y (interior_subset (hK hy))
    apply (sphereSobolevZeroEquiv hO hD).injective
    apply sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)
    exact (hFGraph i y ⟨hK hy,hi⟩).trans (hWGraph i y ⟨hK hy,hi⟩).symm
  · have hf0:f y=0 := image_eq_zero_of_notMem_tsupport (fun hh => hy (hf hh))
    have hW0:W y=0 := image_eq_zero_of_notMem_tsupport (fun hh => hy (hW hh))
    exact hf0.trans hW0.symm

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
