import Calderon.NativeTruncationContinuity

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

lemma continuous_nativePosPart_sub (v : TauCeti.W1p mu Omega 2) :
    Continuous (fun w : TauCeti.W1p mu Omega 2 =>
      TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (w-v)) := by
  exact (continuous_nativePosPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).comp
    (continuous_id.sub continuous_const)

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.continuous_nativePosPart_sub
