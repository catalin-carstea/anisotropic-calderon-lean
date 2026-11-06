import Calderon.NativeSphereL2OrthogonalPullback
import Calderon.SmoothSphereFields

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotation SmoothAngularCasimir SmoothSphereFields CompactParameterSmoothness

/-! Upfront expansion: EXPANSION-finite-harmonic-angle-derivative-v001.json.
Actual continuous-sphere differentiation precedes bounded CLM transport to probability L2. -/

lemma contDiff_coordinateRotationScalarFamily (i j : Fin 3) (F : R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun q : ℝ × R3 => F (coordinateRotation i j q.1 q.2)) := by
  apply hF.comp
  exact contDiff_coordinateRotation i j

def coordinateRotationSphereSection (i j : Fin 3) (F : R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) : ℝ → C(UnitSphere,ℝ) :=
  compactPullback (fun q : ℝ × R3 => F (coordinateRotation i j q.1 q.2))
    (contDiff_coordinateRotationScalarFamily i j F hF).continuous unitSphereInclusion

lemma contDiff_coordinateRotationSphereSection (i j : Fin 3) (F : R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (coordinateRotationSphereSection i j F hF) :=
  contDiff_infty_compactPullback _ (contDiff_coordinateRotationScalarFamily i j F hF) unitSphereInclusion

lemma hasDerivAt_coordinateRotationSphereSection (i j : Fin 3) (F : R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    HasDerivAt (coordinateRotationSphereSection i j F hF)
      (coordinateRotationSphereSection i j (sphereRotationDerivative i j F)
        (contDiff_sphereRotationDerivative i j F hF) t) t := by
  let S : ℝ → C(UnitSphere,ℝ) := coordinateRotationSphereSection i j F hF
  have hS : ContDiff ℝ ∞ S := contDiff_coordinateRotationSphereSection i j F hF
  have hd : HasDerivAt S (deriv S t) t := (hS.differentiable (by simp) t).hasDerivAt
  have he : deriv S t = coordinateRotationSphereSection i j (sphereRotationDerivative i j F)
      (contDiff_sphereRotationDerivative i j F hF) t := by
    apply ContinuousMap.ext
    intro «ω»
    have hEval := (ContinuousMap.evalCLM ℝ «ω» : C(UnitSphere,ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hd
    change HasDerivAt (fun θ : ℝ => F (coordinateRotation i j θ «ω».val)) ((deriv S t) «ω») t at hEval
    exact hEval.unique (hasDerivAt_rotation_comp i j F hF t «ω».val)
  rw [he] at hd
  exact hd

lemma coordinateRotationSphereSection_zero (i j : Fin 3) (F : R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) :
    coordinateRotationSphereSection i j F hF 0 = smoothSphereRestriction F hF := by
  apply ContinuousMap.ext
  intro «ω»
  change F (coordinateRotation i j 0 «ω».val) = F «ω».val
  rw [coordinateRotation_zero]

lemma sphereL2OrthogonalPullback_coordinate_eq_section (i j : Fin 3) (F : R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    sphereL2OrthogonalPullback (coordinateRotationIsometry i j t) (smoothSphereLift F hF) =
      ContinuousMap.toLp 2 sphereProbability ℝ (coordinateRotationSphereSection i j F hF t) := by
  rw [smoothSphereLift,sphereL2OrthogonalPullback_toLp]
  congr 1

lemma contDiff_sphereL2OrthogonalPullback_coordinate_smooth (i j : Fin 3) (F : R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun t => sphereL2OrthogonalPullback (coordinateRotationIsometry i j t)
      (smoothSphereLift F hF)) := by
  simp_rw [sphereL2OrthogonalPullback_coordinate_eq_section]
  apply (ContinuousMap.toLp 2 sphereProbability ℝ : C(UnitSphere,ℝ) →L[ℝ] SphereL2).contDiff.comp
  exact contDiff_coordinateRotationSphereSection i j F hF

lemma hasDerivAt_sphereL2OrthogonalPullback_coordinate_smooth (i j : Fin 3) (F : R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    HasDerivAt (fun θ => sphereL2OrthogonalPullback (coordinateRotationIsometry i j θ)
      (smoothSphereLift F hF))
      (sphereL2OrthogonalPullback (coordinateRotationIsometry i j t)
        (smoothSphereLift (sphereRotationDerivative i j F)
          (contDiff_sphereRotationDerivative i j F hF))) t := by
  have hd := (ContinuousMap.toLp 2 sphereProbability ℝ : C(UnitSphere,ℝ) →L[ℝ] SphereL2).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_coordinateRotationSphereSection i j F hF t)
  change HasDerivAt (fun θ => ContinuousMap.toLp 2 sphereProbability ℝ
    (coordinateRotationSphereSection i j F hF θ))
    (ContinuousMap.toLp 2 sphereProbability ℝ (coordinateRotationSphereSection i j
      (sphereRotationDerivative i j F) (contDiff_sphereRotationDerivative i j F hF) t)) t at hd
  simp_rw [← sphereL2OrthogonalPullback_coordinate_eq_section] at hd
  exact hd

lemma sphereL2OrthogonalPullback_coordinate_zero_smooth (i j : Fin 3) (F : R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) :
    sphereL2OrthogonalPullback (coordinateRotationIsometry i j 0) (smoothSphereLift F hF) =
      smoothSphereLift F hF := by
  rw [sphereL2OrthogonalPullback_coordinate_eq_section,coordinateRotationSphereSection_zero]
  rfl

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.contDiff_coordinateRotationScalarFamily
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.coordinateRotationSphereSection
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.contDiff_coordinateRotationSphereSection
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.hasDerivAt_coordinateRotationSphereSection
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.coordinateRotationSphereSection_zero
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereL2OrthogonalPullback_coordinate_eq_section
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.contDiff_sphereL2OrthogonalPullback_coordinate_smooth
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.hasDerivAt_sphereL2OrthogonalPullback_coordinate_smooth
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereL2OrthogonalPullback_coordinate_zero_smooth
