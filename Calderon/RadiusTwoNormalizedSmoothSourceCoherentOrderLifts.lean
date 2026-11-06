import Calderon.RadiusTwoNormalizedSmoothSourceOrderLift

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution radiusTwoNativeZeroDilation

lemma exists_coherent_radiusTwoNormalizedSmoothSource_order_lifts
    (hreg : FixedDirichletRegularity) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (F : SmoothData) :
    ∃ U : (s : ℕ) → BallSobolev (s+2),
      (∀ s : ℕ, TauCeti.Wkp.firstOrder (s+1) (U s) =
        (radiusTwoNativeZeroDilation
          (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)) : BallH1)) ∧
      (∀ s : ℕ, TauCeti.Wkp.lowerOrder (s+2) (U (s+1)) = U s) := by
  choose U hU using (fun s : ℕ => exists_radiusTwoNormalizedSmoothSource_order_lift hreg g hg s F)
  have hV (s : ℕ) : TauCeti.Wkp.value (s+2) (U s) =
      TauCeti.W1p.value (radiusTwoNativeZeroDilation
        (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)) : BallH1) := by
    simpa only [TauCeti.Wkp.value_firstOrder] using
      congrArg (fun w : BallH1 => TauCeti.W1p.value w) (hU s)
  refine ⟨U,hU,?_⟩
  intro s
  apply TauCeti.Wkp.ext (s+2)
  exact (TauCeti.Wkp.value_succ (s+2) (U (s+1))).symm.trans
    ((hV (s+1)).trans (hV s).symm)

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_coherent_radiusTwoNormalizedSmoothSource_order_lifts
