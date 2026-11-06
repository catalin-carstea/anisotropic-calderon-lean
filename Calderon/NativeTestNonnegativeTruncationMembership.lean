import Calderon.NativeTestNonnegativeTruncationValues
import TauCeti.Analysis.Sobolev.W1p.CompactSupport

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E}

lemma nativeTest_posPart_sub_mem_w1p0Submodule
    (phi : 𝓓(Omega, ℝ)) (v : TauCeti.W1p mu Omega 2)
    (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ TauCeti.W1p.value v x) :
    TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (TauCeti.W1p.ofTestFunctionₗ mu Omega 2 phi-v) ∈
      TauCeti.w1p0Submodule mu Omega 2 := by
  exact TauCeti.W1p.mem_w1p0Submodule_of_isCompact
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) phi.hasCompactSupport phi.tsupport_subset
    (nativeTest_posPart_sub_zero_off_tsupport_ae phi v hv)

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.nativeTest_posPart_sub_mem_w1p0Submodule
