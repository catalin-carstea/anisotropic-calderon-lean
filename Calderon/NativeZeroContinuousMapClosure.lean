import TauCeti.Analysis.Sobolev.W1p.Zero

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E}

lemma native_zero_mem_of_continuous_map
    (F : TauCeti.W1p mu Omega 2 → TauCeti.W1p mu Omega 2) (hF : Continuous F)
    (hTest : ∀ phi : 𝓓(Omega, ℝ), F (TauCeti.W1p.ofTestFunctionₗ mu Omega 2 phi) ∈
      TauCeti.w1p0Submodule mu Omega 2)
    (u : TauCeti.W1p mu Omega 2) (hu : u ∈ TauCeti.w1p0Submodule mu Omega 2) :
    F u ∈ TauCeti.w1p0Submodule mu Omega 2 := by
  exact TauCeti.w1p0Submodule_subset_of_isClosed
    ((TauCeti.w1p0Submodule mu Omega 2).isClosed.preimage hF) hTest hu

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.native_zero_mem_of_continuous_map
