import Calderon.OrthogonalSphereMeasure
import Calderon.SmoothAngularCasimir
import Calderon.NativeOrthogonalSmoothPullback

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.SphereHarmonic
open OrthogonalSphereMeasure SmoothAngularCasimir DirichletFamily.DriftBootstrap

/-! Expanded before source in EXPANSION-native-finite-sphere-orthogonal-trace-v001.json. -/

def sphereL2OrthogonalPullback (e : R3 ≃ₗᵢ[ℝ] R3) : SphereL2 →ₗᵢ[ℝ] SphereL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (orthogonalSphereHomeomorph e)
    (orthogonalSphereHomeomorph_sphereProbability_preserving e)

lemma sphereL2OrthogonalPullback_toLp (e : R3 ≃ₗᵢ[ℝ] R3) (f : C(UnitSphere,ℝ)) :
    sphereL2OrthogonalPullback e (ContinuousMap.toLp 2 sphereProbability ℝ f) =
      ContinuousMap.toLp 2 sphereProbability ℝ
        (f.comp ⟨orthogonalSphereHomeomorph e,(orthogonalSphereHomeomorph e).continuous⟩) := by
  apply Lp.ext
  have hComp := Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp 2 sphereProbability ℝ f)
    (orthogonalSphereHomeomorph_sphereProbability_preserving e)
  have hRep := (orthogonalSphereHomeomorph_sphereProbability_preserving e).quasiMeasurePreserving.ae_eq_comp
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) sphereProbability f)
  have hOut := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) sphereProbability
    (f.comp ⟨orthogonalSphereHomeomorph e,(orthogonalSphereHomeomorph e).continuous⟩)
  filter_upwards [hComp,hRep,hOut] with «ω» h1 h2 h3
  exact h1.trans (h2.trans h3.symm)

lemma sphereL2OrthogonalPullback_smoothSphereLift (e : R3 ≃ₗᵢ[ℝ] R3)
    (f : OAI.AnisotropicCalderon.EnergyBridge.SmoothData) :
    sphereL2OrthogonalPullback e (smoothSphereLift f.1 f.2) =
      smoothSphereLift (orthogonalSmoothPullback e f).1 (orthogonalSmoothPullback e f).2 := by
  rw [smoothSphereLift,sphereL2OrthogonalPullback_toLp]
  congr 1


end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereL2OrthogonalPullback
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereL2OrthogonalPullback_toLp
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereL2OrthogonalPullback_smoothSphereLift
