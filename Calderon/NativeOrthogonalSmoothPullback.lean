import Calderon.MetricPullbackFlux
import Calderon.SmoothSobolevBridge
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricOperator

/-! Pullback convention is f(e x), with e a real linear isometry equivalence. -/

def orthogonalSmoothPullback (e : R3 ≃ₗᵢ[ℝ] R3) (f : SmoothData) : SmoothData :=
  ⟨f.1 ∘ e,f.2.comp e.toContinuousLinearEquiv.toContinuousLinearMap.contDiff⟩

lemma gradient_comp_orthogonal (e : R3 ≃ₗᵢ[ℝ] R3) (f : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (x : R3) :
    gradient (f ∘ e) x = e.symm (gradient f (e x)) := by
  have h := gradient_comp_eq_adjoint e.toContinuousLinearEquiv.toContinuousLinearMap f
    e.toContinuousLinearEquiv.toContinuousLinearMap.contDiff hf x
  rw [e.toContinuousLinearEquiv.toContinuousLinearMap.fderiv,e.adjoint_eq_symm] at h
  exact h

lemma orthogonal_preimage_unitBall (e : R3 ≃ₗᵢ[ℝ] R3) :
    e ⁻¹' (ballOpens : Set R3) = (ballOpens : Set R3) := by
  ext x
  change dist (e x) (0 : R3) < 1 ↔ dist x (0 : R3) < 1
  rw [dist_zero_right,dist_zero_right,e.norm_map]

lemma orthogonal_measurePreserving_unitBall (e : R3 ≃ₗᵢ[ℝ] R3) :
    MeasurePreserving e ((volume : Measure R3).restrict ballOpens)
      ((volume : Measure R3).restrict ballOpens) := by
  refine ⟨e.continuous.measurable,?_⟩
  have h := Measure.restrict_map (μ := (volume : Measure R3))
    e.continuous.measurable ballOpens.isOpen.measurableSet
  rw [e.measurePreserving.map_eq,orthogonal_preimage_unitBall] at h
  exact h.symm

lemma integral_comp_orthogonal_unitBall (e : R3 ≃ₗᵢ[ℝ] R3) (f : R3 → ℝ) :
    ∫ x in (ballOpens : Set R3), f (e x) = ∫ x in (ballOpens : Set R3), f x :=
  (orthogonal_measurePreserving_unitBall e).integral_comp e.toHomeomorph.measurableEmbedding f

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.orthogonalSmoothPullback
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.gradient_comp_orthogonal
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.orthogonal_preimage_unitBall
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.orthogonal_measurePreserving_unitBall
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.integral_comp_orthogonal_unitBall
