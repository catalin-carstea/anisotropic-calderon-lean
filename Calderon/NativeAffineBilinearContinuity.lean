import Calderon.NativeZeroRestrictionNegation

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem continuous_nativeAffineForcing_of_bilinear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] BallH1 →L[ℝ] BallH1 →L[ℝ] ℝ) :
    Continuous (fun p : E × BallH1 =>
      -((B p.1 p.2).comp
        (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL)) := by
  have hFull : Continuous (fun p : E × BallH1 => B p.1 p.2) :=
    (B.continuous.comp continuous_fst).clm_apply continuous_snd
  exact continuous_neg_restrict_nativeFunctionals.comp hFull

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_nativeAffineForcing_of_bilinear
