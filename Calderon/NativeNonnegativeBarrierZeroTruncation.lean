import Calderon.NativeZeroContinuousMapClosure
import Calderon.NativePositivePartSubContinuity
import Calderon.NativeTestNonnegativeTruncationMembership

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E}

attribute [local irreducible] TauCeti.W1p.posPart TauCeti.W1p.posPartAbove

lemma posPart_sub_mem_w1p0Submodule_of_nonneg
    (u v : TauCeti.W1p mu Omega 2)
    (hu : u ∈ TauCeti.w1p0Submodule mu Omega 2)
    (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ TauCeti.W1p.value v x) :
    TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (u-v) ∈
      TauCeti.w1p0Submodule mu Omega 2 := by
  exact native_zero_mem_of_continuous_map
    (fun w : TauCeti.W1p mu Omega 2 =>
      TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (w-v))
    (continuous_nativePosPart_sub v)
    (fun phi => nativeTest_posPart_sub_mem_w1p0Submodule phi v hv) u hu

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.posPart_sub_mem_w1p0Submodule_of_nonneg
