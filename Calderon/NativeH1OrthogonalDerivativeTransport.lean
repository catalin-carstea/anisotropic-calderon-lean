import Calderon.NativeH1OrthogonalPullback

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

lemma value_smoothSobolev_orthogonal (e : R3 ≃ₗᵢ[ℝ] R3) (f : SmoothData) :
    TauCeti.W1p.value (smoothSobolev (orthogonalSmoothPullback e f)) =
      Lp.compMeasurePreserving e (orthogonal_measurePreserving_unitBall e)
        (TauCeti.W1p.value (smoothSobolev f)) := by
  apply Lp.ext
  have hv := (orthogonal_measurePreserving_unitBall e).quasiMeasurePreserving.ae_eq_comp
    (value_smoothSobolev_ae f)
  filter_upwards [value_smoothSobolev_ae (orthogonalSmoothPullback e f),
    Lp.coeFn_compMeasurePreserving (TauCeti.W1p.value (smoothSobolev f))
      (orthogonal_measurePreserving_unitBall e),hv] with x hl hc hx
  exact hl.trans (hc.trans hx).symm

lemma gradient_smoothSobolev_orthogonal (e : R3 ≃ₗᵢ[ℝ] R3) (f : SmoothData) :
    TauCeti.W1p.gradient (smoothSobolev (orthogonalSmoothPullback e f)) =
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp
        (Lp.compMeasurePreserving e (orthogonal_measurePreserving_unitBall e)
          (TauCeti.W1p.gradient (smoothSobolev f))) := by
  apply Lp.ext
  have hv := (orthogonal_measurePreserving_unitBall e).quasiMeasurePreserving.ae_eq_comp
    (gradient_smoothSobolev_ae f)
  filter_upwards [gradient_smoothSobolev_ae (orthogonalSmoothPullback e f),
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
      (Lp.compMeasurePreserving e (orthogonal_measurePreserving_unitBall e)
        (TauCeti.W1p.gradient (smoothSobolev f))),
    Lp.coeFn_compMeasurePreserving (TauCeti.W1p.gradient (smoothSobolev f))
      (orthogonal_measurePreserving_unitBall e),hv] with x hl hg hc hx
  change TauCeti.W1p.gradient (smoothSobolev (orthogonalSmoothPullback e f)) x =
    gradient (f.1 ∘ e) x at hl
  exact (hl.trans (gradient_comp_orthogonal e f.1 f.2 x)).trans
    (hg.trans (congrArg e.symm (hc.trans hx))).symm

lemma value_nativeH1OrthogonalPullback (e : R3 ≃ₗᵢ[ℝ] R3) (u : BallH1) :
    TauCeti.W1p.value (nativeH1OrthogonalPullback e u) =
      Lp.compMeasurePreserving e (orthogonal_measurePreserving_unitBall e)
        (TauCeti.W1p.value u) := by
  refine denseRange_nativeSmoothSobolevLinear.induction_on u
    (isClosed_eq
      (TauCeti.W1p.valueL.continuous.comp (nativeH1OrthogonalPullback e).continuous)
      ((Lp.compMeasurePreservingₗᵢ ℝ e (orthogonal_measurePreserving_unitBall e)).continuous.comp
        TauCeti.W1p.valueL.continuous)) ?_
  intro f
  change TauCeti.W1p.value (nativeH1OrthogonalPullback e (smoothSobolev ⟨f.1,f.2⟩)) = _
  rw [nativeH1OrthogonalPullback_smoothSobolev]
  exact value_smoothSobolev_orthogonal e ⟨f.1,f.2⟩

lemma gradient_nativeH1OrthogonalPullback (e : R3 ≃ₗᵢ[ℝ] R3) (u : BallH1) :
    TauCeti.W1p.gradient (nativeH1OrthogonalPullback e u) =
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp
        (Lp.compMeasurePreserving e (orthogonal_measurePreserving_unitBall e)
          (TauCeti.W1p.gradient u)) := by
  refine denseRange_nativeSmoothSobolevLinear.induction_on u
    (isClosed_eq
      (TauCeti.W1p.gradientL.continuous.comp (nativeH1OrthogonalPullback e).continuous)
      ((e.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2
        ((volume : Measure R3).restrict ballOpens)).continuous.comp
          ((Lp.compMeasurePreservingₗᵢ ℝ e (orthogonal_measurePreserving_unitBall e)).continuous.comp
            TauCeti.W1p.gradientL.continuous))) ?_
  intro f
  change TauCeti.W1p.gradient (nativeH1OrthogonalPullback e (smoothSobolev ⟨f.1,f.2⟩)) = _
  rw [nativeH1OrthogonalPullback_smoothSobolev]
  exact gradient_smoothSobolev_orthogonal e ⟨f.1,f.2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.value_smoothSobolev_orthogonal
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.gradient_smoothSobolev_orthogonal
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.value_nativeH1OrthogonalPullback
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.gradient_nativeH1OrthogonalPullback
